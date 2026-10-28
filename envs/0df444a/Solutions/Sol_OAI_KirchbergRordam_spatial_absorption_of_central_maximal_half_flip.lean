-- Prove2me | solution 1 for OAI.KirchbergRordam.spatial_absorption_of_central_maximal_half_flip
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T17:28:46.940502+00:00
-- url     : https://prove2.me/submissions/b8dbbda5-9f03-451c-b99d-c243cf91fcb1

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr013
import Theorems.Thm_OAI_KirchbergRordam_quotient_isomorphism_of_ultrapower_split_and_conjugacy

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_NormUltrapower
attribute [-instance] _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]


open Filter Topology BoundedContinuousFunction

universe uQuot

namespace KirchbergRordam
namespace NormUltrapower

variable {A : Type*} [CStarAlgebra A]


theorem normLimit_nonneg (ω : Ultrafilter ℕ) (x : BoundedSeq A) : 0 ≤ normLimit ω x :=
  (exists_norm_limit ω x).choose_spec.1.1

theorem normLimit_le (ω : Ultrafilter ℕ) (x : BoundedSeq A) : normLimit ω x ≤ ‖x‖ :=
  (exists_norm_limit ω x).choose_spec.1.2

theorem normLimit_add_le (ω : Ultrafilter ℕ) (x y : BoundedSeq A) :
    normLimit ω (x + y) ≤ normLimit ω x + normLimit ω y := by
  exact le_of_tendsto_of_tendsto (tendsto_norm ω (x+y))
    ((tendsto_norm ω x).add (tendsto_norm ω y))
    (Eventually.of_forall fun n => norm_add_le (x n) (y n))

theorem normLimit_sub_le (ω : Ultrafilter ℕ) (x y : BoundedSeq A) :
    normLimit ω x - normLimit ω y ≤ normLimit ω (x-y) := by
  have h := normLimit_add_le ω (x-y) y
  rw [sub_add_cancel] at h
  linarith


theorem normLimit_eq_of_sub_mem (ω : Ultrafilter ℕ) {x y : BoundedSeq A}
    (h : x-y ∈ nullIdeal ω) : normLimit ω x = normLimit ω y := by
  change normLimit ω (x-y) = 0 at h
  apply le_antisymm
  · have h' := normLimit_sub_le ω x y
    linarith
  · have h' := normLimit_sub_le ω y x
    rw [← neg_sub x y, normLimit_neg, h] at h'
    linarith


theorem normLimit_le_quotient (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    normLimit ω x ≤ ‖Ideal.Quotient.mk (nullIdeal ω) x‖ := by
  apply QuotientAddGroup.le_norm_iff.mpr
  intro y hy
  have h : y-x ∈ nullIdeal ω := (Ideal.Quotient.eq).mp hy
  rw [← normLimit_eq_of_sub_mem ω h]
  exact normLimit_le ω y


theorem cutRepresentative_norm_le (x : BoundedSeq A) (c : ℝ) (hc : 0 ≤ c) :
    ‖cutRepresentative x c hc‖ ≤ c := by
  apply (BoundedContinuousFunction.norm_le hc).mpr
  intro n
  change ‖if ‖x n‖ < c then x n else 0‖ ≤ c
  split_ifs with h
  · exact h.le
  · simpa only [norm_zero] using hc

theorem cutRepresentative_mk_eq (ω : Ultrafilter ℕ) (x : BoundedSeq A)
    (c : ℝ) (hc : 0 ≤ c) (hlim : normLimit ω x < c) :
    Ideal.Quotient.mk (nullIdeal ω) x =
      Ideal.Quotient.mk (nullIdeal ω) (cutRepresentative x c hc) := by
  rw [Ideal.Quotient.eq, mem_nullIdeal]
  have he : ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ < c :=
    (tendsto_norm ω x).eventually (eventually_lt_nhds hlim)
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) (ω : Filter ℕ) (𝓝 0) := tendsto_const_nhds
  apply hz.congr'
  filter_upwards [he] with n hn
  change (0 : ℝ) = ‖x n - (if ‖x n‖ < c then x n else 0)‖
  rw [ite_eq_left hn, sub_self, norm_zero]


theorem quotient_norm_le_normLimit (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    ‖Ideal.Quotient.mk (nullIdeal ω) x‖ ≤ normLimit ω x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hpos : 0 ≤ normLimit ω x + ε := add_nonneg (normLimit_nonneg ω x) hε.le
  rw [cutRepresentative_mk_eq ω x (normLimit ω x + ε) hpos (lt_add_of_pos_right _ hε)]
  have hb := Submodule.Quotient.norm_mk_le (nullIdeal ω)
    (cutRepresentative x (normLimit ω x + ε) hpos)
  exact hb.trans (cutRepresentative_norm_le x (normLimit ω x + ε) hpos)


theorem norm_mk_eq (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    ‖Ideal.Quotient.mk (nullIdeal ω) x‖ = normLimit ω x :=
  le_antisymm (quotient_norm_le_normLimit ω x) (normLimit_le_quotient ω x)


theorem normLimit_const (ω : Ultrafilter ℕ) (a : A) :
    normLimit ω (constantSeq a) = ‖a‖ :=
  tendsto_nhds_unique (tendsto_norm ω (constantSeq a)) tendsto_const_nhds

@[simp]
theorem norm_diagonal (ω : Ultrafilter ℕ) (a : A) : ‖diagonal ω a‖ = ‖a‖ := by
  change ‖Ideal.Quotient.mk (nullIdeal ω) (constantSeq a)‖ = ‖a‖
  rw [norm_mk_eq, normLimit_const]

theorem diagonal_isometry (ω : Ultrafilter ℕ) : Isometry (diagonal (A := A) ω) := by
  apply Isometry.of_dist_eq
  intro a b
  rw [dist_eq_norm, ← map_sub, norm_diagonal, dist_eq_norm]

instance quotientNontrivial (ω : Ultrafilter ℕ) [Nontrivial A] : Nontrivial (Algebra A ω) :=
  (diagonal_isometry ω).injective.nontrivial


instance centralNontrivial (ω : Ultrafilter ℕ) [Nontrivial A] :
    Nontrivial (CentralAlgebra A ω) := inferInstance

theorem mem_central_iff (ω : Ultrafilter ℕ) (z : Algebra A ω) :
    z ∈ centralSubalgebra ω ↔ ∀ a : A, diagonal ω a * z = z * diagonal ω a := by
  change z ∈ StarSubalgebra.centralizer ℂ (Set.range (diagonal ω)) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h a
    exact (h (diagonal ω a) ⟨a, rfl⟩).1
  · intro h x hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨h a, by simpa only [map_star] using h (star a)⟩


end NormUltrapower
end KirchbergRordam
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Absorption
attribute [-instance] _root_.OAI.KirchbergRordam.MinTensor.instCStarRingAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam.SeparableReduction
open Set Topology TopologicalSpace
variable {A : Type*} [CStarAlgebra A]


lemma stage_separable {s : Set A} (hs : IsSeparable s) (n : ℕ) : IsSeparable (stage s n) := by
  induction n with
  | zero => exact hs.union (isSeparable_range (continuous_algebraMap ℂ A))
  | succ n ih => exact ((ih.union ((ih.prod ih).image (continuous_fst.add continuous_snd))).union
      ((ih.prod ih).image (continuous_fst.mul continuous_snd))).union (ih.image continuous_star)
lemma adjoin_separable {s : Set A} (hs : IsSeparable s) :
    IsSeparable (StarAlgebra.adjoin ℂ s : Set A) := by
  have ht : StarAlgebra.adjoin ℂ s ≤ termAlgebra s := StarAlgebra.adjoin_le
    (fun a ha=>mem_iUnion.mpr ⟨0,Or.inl ha⟩)
  exact (IsSeparable.iUnion (stage_separable hs)).mono ht


lemma closedAdjoin_separable {s : Set A} (hs : IsSeparable s) :
    IsSeparable ((StarAlgebra.adjoin ℂ s).topologicalClosure : Set A) :=
  (adjoin_separable hs).closure
end KirchbergRordam.SeparableReduction

namespace KirchbergRordam.MaxTensor
open Topology TopologicalSpace
open scoped CStarAlgebra
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]


theorem separable_maxTensor [SeparableSpace A] [SeparableSpace B] :
    SeparableSpace (Algebra A B) := by
  let s : Set (Algebra A B) := Set.range (includeLeft (A := A) (B := B)) ∪
    Set.range (includeRight (A := A) (B := B))
  let T := (StarAlgebra.adjoin ℂ s).topologicalClosure
  have hsep : IsSeparable (T : Set (Algebra A B)) :=
    SeparableReduction.closedAdjoin_separable ((isSeparable_range (map_continuous includeLeft)).union
      (isSeparable_range (map_continuous includeRight)))
  have hinc : s ⊆ T := (StarAlgebra.subset_adjoin ℂ s).trans
    (StarSubalgebra.le_topologicalClosure _)
  have hall (x : Algebra A B) : x ∈ T := by
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact StarSubalgebra.isClosed_topologicalClosure _
    | ih x =>
      change of x ∈ T
      suffices ∀ tensor : A ⊗[ℂ] B, of (rawEquiv tensor) ∈ T from
        this (rawEquiv.symm x)
      intro tensor
      induction tensor using OAI.tensorInductionOn with
      | tmul a b =>
        change of (a ⊗ₜ[ℂ] b) ∈ T
        rw [of_tmul]
        exact T.mul_mem (hinc (Or.inl ⟨a,rfl⟩)) (hinc (Or.inr ⟨b,rfl⟩))
      | add x y hx hy =>
        simp only [map_add]
        exact T.add_mem hx hy
  exact isSeparable_univ_iff.mp (hsep.mono (fun x _ => hall x))

end KirchbergRordam.MaxTensor
namespace KirchbergRordam.MaxTensor
open Filter Topology


theorem pointwise_limit_of_tensor_legs
    {A D C : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra C]
    (F : ℕ → Algebra A D →⋆ₐ[ℂ] C) (g : Algebra A D →⋆ₐ[ℂ] C)
    (hL : ∀ a, Tendsto (fun n => F n (includeLeft a)) atTop (𝓝 (g (includeLeft a))))
    (hR : ∀ d, Tendsto (fun n => F n (includeRight d)) atTop (𝓝 (g (includeRight d)))) :
    ∀ b, Tendsto (fun n => F n b) atTop (𝓝 (g b)) := by
  have hEq : Equicontinuous (fun n b => F n b) := by
    apply Metric.equicontinuous_of_continuity_modulus id tendsto_id
    intro b c n
    change dist (F n b) (F n c) ≤ dist b c
    rw [dist_eq_norm,← map_sub,dist_eq_norm]
    exact NonUnitalStarAlgHom.norm_apply_le (F n) (b-c)
  have hg : LipschitzWith 1 g := by
    apply LipschitzWith.of_dist_le_mul
    intro b c
    simp only [NNReal.coe_one,one_mul]
    rw [dist_eq_norm,← map_sub,dist_eq_norm]
    exact NonUnitalStarAlgHom.norm_apply_le g (b-c)
  have hclosed := hEq.isClosed_setOfPred_tendsto (l := atTop) hg.continuous
  intro b
  induction b using UniformSpace.Completion.induction_on with
  | hp => exact hclosed
  | ih x =>
    change Tendsto (fun n => F n (of x)) atTop (𝓝 (g (of x)))
    suffices ∀ tensor : A ⊗[ℂ] D,
        Tendsto (fun n => F n (of (rawEquiv tensor))) atTop
          (𝓝 (g (of (rawEquiv tensor)))) from this (rawEquiv.symm x)
    intro tensor
    induction tensor using OAI.tensorInductionOn with
    | tmul a d =>
      change Tendsto (fun n => F n (of (a ⊗ₜ[ℂ] d))) atTop
        (𝓝 (g (of (a ⊗ₜ[ℂ] d))))
      simpa only [of_tmul,map_mul] using (hL a).mul (hR d)
    | add x y hx hy =>
      simpa only [map_add] using hx.add hy
end KirchbergRordam.MaxTensor
namespace KirchbergRordam
open NormUltrapower
open scoped CStarAlgebra TensorProduct
lemma ultrapower_left_commutes_right
    {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
    (ω : Ultrafilter ℕ) (x : NormUltrapower.Algebra A ω) (d : D) :
    Commute (NormUltrapower.map (MaxTensor.includeLeft (B := D)) ω x)
      (NormUltrapower.diagonal ω (MaxTensor.includeRight (A := A) d)) := by
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective x
  change Commute (NormUltrapower.map (MaxTensor.includeLeft (B := D)) ω (quotientMap ω y))
    (NormUltrapower.diagonal ω (MaxTensor.includeRight (A := A) d))
  rw [NormUltrapower.map_mk]
  change quotientMap ω (sequenceMap MaxTensor.includeLeft y) * quotientMap ω (constantSeq (MaxTensor.includeRight d)) =
    quotientMap ω (constantSeq (MaxTensor.includeRight d)) * quotientMap ω (sequenceMap MaxTensor.includeLeft y)
  rw [← map_mul,← map_mul]
  congr 1
  ext n
  exact (MaxTensor.legs_commute (y n) d).eq
lemma maximal_lift_image_commutes
    {A D C : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra C]
    (L : A →⋆ₐ[ℂ] C) (R : D →⋆ₐ[ℂ] C) (hcomm : ∀ a d, Commute (L a) (R d))
    (c : C) (hL : ∀ a, Commute c (L a)) (hR : ∀ d, Commute c (R d))
    (x : MaxTensor.Algebra A D) : Commute c (MaxTensor.lift L R hcomm x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_const.mul (map_continuous (MaxTensor.lift L R hcomm)))
      ((map_continuous (MaxTensor.lift L R hcomm)).mul continuous_const)
  | ih x =>
    change Commute c (MaxTensor.lift L R hcomm (MaxTensor.of x))
    suffices ∀ tensor : A ⊗[ℂ] D,
        Commute c (MaxTensor.lift L R hcomm (MaxTensor.of (MaxTensor.rawEquiv tensor))) from
      this (MaxTensor.rawEquiv.symm x)
    intro tensor
    induction tensor using OAI.tensorInductionOn with
    | tmul a d =>
      change Commute c (MaxTensor.lift L R hcomm (MaxTensor.of (a ⊗ₜ[ℂ] d)))
      rw [MaxTensor.lift_of_tmul]
      exact (hL a).mul_right (hR d)
    | add x y hx hy => simpa only [map_add] using hx.add_right hy
end KirchbergRordam

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MinTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
section
open scoped CStarAlgebra ComplexOrder

open scoped TensorProduct InnerProductSpace
open UniformSpace
namespace KirchbergRordam.Spatial
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]


lemma map_mul (T U : H →L[ℂ] H) (S V : K →L[ℂ] K) :
    map (T * U) (S * V) = map T S * map U V := by
  apply ext
  intro x
  simp only [mul_apply_eq_comp, map_coe, TensorProduct.mapL_mul]

end KirchbergRordam.Spatial

end
namespace KirchbergRordam.MinTensor
open scoped TensorProduct
universe u


attribute [instance] RepresentationPair.normH RepresentationPair.innerH
  RepresentationPair.completeH RepresentationPair.normK RepresentationPair.innerK
  RepresentationPair.completeK


end KirchbergRordam.MinTensor
namespace KirchbergRordam.MinTensor
open scoped TensorProduct
universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
lemma seminorm_tmul_le (a : A) (b : B) : seminorm (a ⊗ₜ[ℂ] b) ≤ ‖a‖ * ‖b‖ :=
  seminorm_le fun ρ => (spatialIndex ρ).tmul_le a b
end KirchbergRordam.MinTensor

namespace KirchbergRordam.MinTensor
open scoped TensorProduct CStarAlgebra
universe u
variable (A B : Type u) [CStarAlgebra A] [CStarAlgebra B]

variable {A B}
lemma denseRange_of : DenseRange (of (A := A) (B := B)) :=
  UniformSpace.Completion.denseRange_coe

lemma fromMaximal_denseRange : DenseRange (fromMaximal (A := A) (B := B)) :=
  denseRange_of.mono (by
    rintro _ ⟨x, rfl⟩
    exact ⟨MaxTensor.of (MaxTensor.rawEquiv (rawEquiv.symm x)), by simp⟩)
end KirchbergRordam.MinTensor
namespace KirchbergRordam.States
open scoped ComplexOrder


theorem exists_norming_state (A : Type*) [CStarAlgebra A] [Nontrivial A]
    [PartialOrder A] [StarOrderedRing A] (a : A) :
    ∃ φ : A →ₚ[ℂ] ℂ, φ 1 = 1 ∧ ‖φ (star a * a)‖ = ‖a‖ ^ 2 := by
  let b := star a * a
  have hb : 0 ≤ b := star_mul_self_nonneg a
  let : IsStarNormal b := (IsSelfAdjoint.of_nonneg hb).isStarNormal
  let S := StarAlgebra.elemental ℂ b
  have hs : (‖b‖ : ℂ) ∈ spectrum ℂ b := by
    exact spectrum.algebraMap_mem ℂ (CStarAlgebra.norm_mem_spectrum_of_nonneg hb)
  obtain ⟨χ,hχ⟩ := (StarAlgebra.elemental.bijective_characterSpaceToSpectrum b).surjective
    ⟨(‖b‖ : ℂ),hs⟩
  let g : S →ₐ[ℂ] ℂ := WeakDual.CharacterSpace.equivAlgHom χ
  let : StarHomClass (S →ₐ[ℂ] ℂ) S ℂ := AlgHomClass.instStarHomClass
  have hg : ‖g.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul, AlgHom.coe_toContinuousLinearMap] using NonUnitalStarAlgHom.norm_apply_le g x
  obtain ⟨ψ,hψ,hψnorm⟩ := exists_extension_norm_eq S.toSubalgebra.toSubmodule
    g.toContinuousLinearMap
  have hψ1 : ψ 1 = 1 := by
    exact (hψ (1 : S)).trans (map_one g)
  have hψb : ψ b = (‖b‖ : ℂ) := by
    have hh := congrArg Subtype.val hχ
    exact (hψ ⟨b,StarAlgebra.elemental.self_mem ℂ b⟩).trans hh
  let φ : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ ψ.toLinearMap
    (eval_nonneg ψ (hψnorm.trans_le hg) hψ1)
  refine ⟨φ,hψ1,?_⟩
  change ‖ψ b‖ = ‖a‖ ^ 2
  rw [hψb,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg b)]
  simp only [b,CStarRing.norm_star_mul_self,pow_two]
end KirchbergRordam.States
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_TensorComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.Representations
open scoped InnerProductSpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
lemma gnsVector_norm_sq (φ : A →ₚ[ℂ] ℂ) (a : A) :
    ‖gnsVector φ a‖ ^ 2 = ‖φ (star a*a)‖ := by
  rw [← gnsVector_inner]
  rw [← inner_self_re_eq_norm,inner_self_eq_norm_sq]
lemma gnsVector_unit_norm (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1=1) :
    ‖gnsVector φ 1‖ = 1 := by
  have h := gnsVector_norm_sq φ 1
  simp only [star_one,one_mul,hφ,norm_one] at h
  nlinarith [norm_nonneg (gnsVector φ 1)]
lemma gnsVector_norming_norm (φ : A →ₚ[ℂ] ℂ) (a : A)
    (ha : ‖φ (star a*a)‖=‖a‖^2) : ‖gnsVector φ a‖ = ‖a‖ := by
  have h := (gnsVector_norm_sq φ a).trans ha
  nlinarith [norm_nonneg (gnsVector φ a),norm_nonneg a]
end KirchbergRordam.Representations
namespace KirchbergRordam.MinTensor
open scoped TensorProduct InnerProductSpace
universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
lemma RepresentationPair.tmul_norm (ρ : RepresentationPair A B) (a : A) (b : B) :
    ρ.crossSeminorm.toSeminorm (a ⊗ₜ[ℂ] b) =
      ‖Spatial.map (ρ.leftRep a) (ρ.rightRep b)‖ := by
  change ‖ρ.left a * ρ.right b‖ = _
  change ‖Spatial.map (ρ.leftRep a) 1 * Spatial.map 1 (ρ.rightRep b)‖ = _
  rw [← Spatial.map_mul, mul_one,one_mul]


theorem norm_tmul [Nontrivial A] [Nontrivial B] (a : A) (b : B) :
    ‖of (rawEquiv (a ⊗ₜ[ℂ] b))‖ = ‖a‖ * ‖b‖ := by
  rw [norm_of]
  apply le_antisymm (seminorm_tmul_le a b)
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  obtain ⟨φ,hφ,hφa⟩ := States.exists_norming_state A a
  obtain ⟨ψ,hψ,hψb⟩ := States.exists_norming_state B b
  let ρ : RepresentationPair A B := {
    H := φ.GNS
    K := ψ.GNS
    normH := inferInstance
    innerH := inferInstance
    completeH := inferInstance
    normK := inferInstance
    innerK := inferInstance
    completeK := inferInstance
    leftRep := φ.gnsStarAlgHom
    rightRep := ψ.gnsStarAlgHom }
  let ξ : Spatial.Hilbert φ.GNS ψ.GNS :=
    ((Representations.gnsVector φ 1) ⊗ₜ[ℂ] (Representations.gnsVector ψ 1) : φ.GNS ⊗[ℂ] ψ.GNS)
  have hnξ : ‖ξ‖=1 := by
    simp only [ξ,UniformSpace.Completion.norm_coe,TensorProduct.norm_tmul,
      Representations.gnsVector_unit_norm φ hφ,Representations.gnsVector_unit_norm ψ hψ,
      one_mul]
  have heval : Spatial.map (φ.gnsStarAlgHom a) (ψ.gnsStarAlgHom b) ξ =
      ((Representations.gnsVector φ a) ⊗ₜ[ℂ] (Representations.gnsVector ψ b) : φ.GNS ⊗[ℂ] ψ.GNS) := by
    simp only [ξ, Spatial.map_coe,TensorProduct.mapL_tmul,
      Representations.gnsVector_apply,mul_one]
  have hbound : ‖a‖*‖b‖ ≤ ‖Spatial.map (φ.gnsStarAlgHom a) (ψ.gnsStarAlgHom b)‖ := by
    calc
      ‖a‖*‖b‖ = ‖Spatial.map (φ.gnsStarAlgHom a) (ψ.gnsStarAlgHom b) ξ‖ := by
        rw [heval,UniformSpace.Completion.norm_coe,TensorProduct.norm_tmul,
          Representations.gnsVector_norming_norm φ a hφa,
          Representations.gnsVector_norming_norm ψ b hψb]
      _ ≤ ‖Spatial.map (φ.gnsStarAlgHom a) (ψ.gnsStarAlgHom b)‖*‖ξ‖ :=
        ContinuousLinearMap.le_opNorm _ ξ
      _ = _ := by rw [hnξ,mul_one]
  apply hbound.trans
  calc
    _ = ρ.crossSeminorm.toSeminorm (a ⊗ₜ[ℂ] b) := (ρ.tmul_norm a b).symm
    _ ≤ seminorm (a ⊗ₜ[ℂ] b) := le_seminorm (some ρ) _
lemma includeLeft_isometry [Nontrivial A] [Nontrivial B] :
    Isometry (includeLeft (A := A) (B := B)) := by
  apply AddMonoidHomClass.isometry_of_norm includeLeft
  intro a
  change ‖of (rawEquiv (a ⊗ₜ[ℂ] (1 : B)))‖ = ‖a‖
  rw [norm_tmul,norm_one,mul_one]
end KirchbergRordam.MinTensor
namespace KirchbergRordam
section
universe u
open Filter Topology NormUltrapower


theorem spatial_absorption_of_central_maximal_half_flip_oai
    (A D : Type u) [CStarAlgebra A] [CStarAlgebra D]
    [Nontrivial A] [Nontrivial D]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace D]
    (ω : Ultrafilter ℕ) (ι : D →⋆ₐ[ℂ] CentralAlgebra A ω)
    (u : ℕ → unitary (MaxTensor.Algebra D D))
    (hu : ∀ d, Tendsto (fun n => Unitary.conjStarAlgAut ℂ _ (u n)
      (MaxTensor.includeLeft d)) atTop (𝓝 (MaxTensor.includeRight d))) :
    Nonempty (A ≃⋆ₐ[ℂ] MinTensor.Algebra A D) := by
  classical
  let B := MaxTensor.Algebra A D
  let : TopologicalSpace.SeparableSpace B := MaxTensor.separable_maxTensor
  let φ : A →⋆ₐ[ℂ] B := MaxTensor.includeLeft
  let r : D →⋆ₐ[ℂ] B := MaxTensor.includeRight
  let ι₀ : D →⋆ₐ[ℂ] NormUltrapower.Algebra A ω := (centralSubalgebra ω).subtype.comp ι
  have hc (a : A) (d : D) : Commute (NormUltrapower.diagonal ω a) (ι₀ d) :=
    (mem_central_iff ω (ι d : NormUltrapower.Algebra A ω)).mp (ι d).property a
  let ψ : B →⋆ₐ[ℂ] NormUltrapower.Algebra A ω := MaxTensor.lift (NormUltrapower.diagonal ω) ι₀ hc
  have hs (a : A) : ψ (φ a)=NormUltrapower.diagonal ω a :=
    DFunLike.congr_fun (MaxTensor.lift_includeLeft (NormUltrapower.diagonal ω) ι₀ hc) a
  have hsR (d : D) : ψ (r d)=ι₀ d :=
    DFunLike.congr_fun (MaxTensor.lift_includeRight (NormUltrapower.diagonal ω) ι₀ hc) d
  have hφ : Function.Injective φ := by
    intro a b hab
    apply (diagonal_isometry ω).injective
    rw [← hs a,← hs b,hab]
  let L : D →⋆ₐ[ℂ] NormUltrapower.Algebra B ω := (NormUltrapower.map φ ω).comp ι₀
  let R : D →⋆ₐ[ℂ] NormUltrapower.Algebra B ω := (NormUltrapower.diagonal ω).comp r
  have hLR (d e : D) : Commute (L d) (R e) := ultrapower_left_commutes_right ω (ι₀ d) e
  let U : MaxTensor.Algebra D D →⋆ₐ[ℂ] NormUltrapower.Algebra B ω := MaxTensor.lift L R hLR
  have hUL (d : D) : U (MaxTensor.includeLeft d)=L d :=
    DFunLike.congr_fun (MaxTensor.lift_includeLeft L R hLR) d
  have hUR (d : D) : U (MaxTensor.includeRight d)=R d :=
    DFunLike.congr_fun (MaxTensor.lift_includeRight L R hLR) d
  let v : ℕ → unitary (NormUltrapower.Algebra B ω) := fun n => ⟨U (u n),Unitary.map_mem U (u n).property⟩
  have hUa (a : A) (x : MaxTensor.Algebra D D) : Commute (NormUltrapower.diagonal ω (φ a)) (U x) := by
    apply maximal_lift_image_commutes L R hLR
    · intro d
      have he := congrArg (NormUltrapower.map φ ω) (hc a d).eq
      change NormUltrapower.diagonal ω (φ a)*NormUltrapower.map φ ω (ι₀ d) =
        NormUltrapower.map φ ω (ι₀ d)*NormUltrapower.diagonal ω (φ a)
      simpa only [map_mul,map_diagonal] using he
    · intro d
      exact (MaxTensor.legs_commute a d).map (NormUltrapower.diagonal ω)
  let F : ℕ → B →⋆ₐ[ℂ] NormUltrapower.Algebra B ω := fun n =>
    (Unitary.conjStarAlgAut ℂ _ (v n)).toStarAlgHom.comp ((NormUltrapower.map φ ω).comp ψ)
  have hFL (a : A) : Tendsto (fun n => F n (φ a)) atTop (𝓝 (NormUltrapower.diagonal ω (φ a))) := by
    have he (n : ℕ) : F n (φ a)=NormUltrapower.diagonal ω (φ a) := by
      change Unitary.conjStarAlgAut ℂ _ (v n) (NormUltrapower.map φ ω (ψ (φ a)))=_
      rw [hs,map_diagonal,Unitary.conjStarAlgAut_apply]
      change U (u n)*NormUltrapower.diagonal ω (φ a)*star (U (u n))=NormUltrapower.diagonal ω (φ a)
      rw [← (hUa a (u n)).eq,mul_assoc]
      have hv : U (u n)*star (U (u n))=1 := (v n).property.2
      rw [hv,mul_one]
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => NormUltrapower.diagonal ω (φ a)) atTop (𝓝 (NormUltrapower.diagonal ω (φ a))))
  have hFR (d : D) : Tendsto (fun n => F n (r d)) atTop (𝓝 (NormUltrapower.diagonal ω (r d))) := by
    have he (n : ℕ) : F n (r d)=U (Unitary.conjStarAlgAut ℂ _ (u n) (MaxTensor.includeLeft d)) := by
      change Unitary.conjStarAlgAut ℂ _ (v n) (NormUltrapower.map φ ω (ψ (r d)))=_
      rw [hsR]
      simp only [Unitary.conjStarAlgAut_apply,map_mul,map_star,hUL]
      rfl
    have hU : LipschitzWith 1 U := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [NNReal.coe_one,one_mul]
      rw [dist_eq_norm,← map_sub,dist_eq_norm]
      exact NonUnitalStarAlgHom.norm_apply_le U (x-y)
    have ht := (hU.continuous.tendsto (MaxTensor.includeRight d)).comp (hu d)
    rw [hUR] at ht
    change Tendsto (fun n => U (Unitary.conjStarAlgAut ℂ _ (u n) (MaxTensor.includeLeft d)))
      atTop (𝓝 (NormUltrapower.diagonal ω (r d))) at ht
    exact ht.congr (fun n => (he n).symm)
  have hF := MaxTensor.pointwise_limit_of_tensor_legs F (NormUltrapower.diagonal ω) hFL hFR
  let q : B →⋆ₐ[ℂ] MinTensor.Algebra A D := MinTensor.fromMaximal
  have hqd : DenseRange q := MinTensor.fromMaximal_denseRange
  have hqL : LipschitzWith 1 q := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one,one_mul]
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact NonUnitalStarAlgHom.norm_apply_le q (x-y)
  let : TopologicalSpace.SeparableSpace (MinTensor.Algebra A D) :=
    hqd.separableSpace hqL.continuous
  have hleg : q.comp φ = MinTensor.includeLeft :=
    MaxTensor.lift_includeLeft MinTensor.includeLeft MinTensor.includeRight MinTensor.legs_commute
  have hqi : Function.Injective (q.comp φ) := by
    rw [hleg]
    exact MinTensor.includeLeft_isometry.injective
  apply quotient_isomorphism_of_ultrapower_split_and_conjugacy ω φ q hqd hqi ψ hs
  intro T ε hε
  have htest (b : B) (_ : b ∈ T) : ∀ᶠ n in atTop, dist (F n b) (NormUltrapower.diagonal ω b)<ε :=
    (hF b).eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨n,hn⟩ := (T.eventually_all.mpr htest).exists
  exact ⟨v n,hn⟩
end
universe u
open Filter Topology NormUltrapower


end KirchbergRordam

end

end OAI
end

theorem solution.{u} : type_of% @OAI.KirchbergRordam.spatial_absorption_of_central_maximal_half_flip_oai.{u} := @OAI.KirchbergRordam.spatial_absorption_of_central_maximal_half_flip_oai.{u}
