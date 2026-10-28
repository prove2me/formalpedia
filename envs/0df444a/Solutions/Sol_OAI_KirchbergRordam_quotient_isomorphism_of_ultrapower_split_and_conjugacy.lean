-- Prove2me | solution 1 for OAI.KirchbergRordam.quotient_isomorphism_of_ultrapower_split_and_conjugacy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T17:15:49.079695+00:00
-- url     : https://prove2.me/submissions/c6daa8b3-128b-4fbf-a23f-0a9b2196b98b

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr012

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


end NormUltrapower
end KirchbergRordam
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_UltrapowerSaturation
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

namespace KirchbergRordam.NormUltrapower
open Filter Topology BoundedContinuousFunction
open scoped CStarAlgebra
lemma map_positive {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    (φ : A →⋆ₐ[ℂ] B) {a : A} (ha : 0 ≤ a) : 0 ≤ φ a := by
  have hs := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq
  have he : a = star (CFC.sqrt a)*CFC.sqrt a := by rw [hs,CFC.sqrt_mul_sqrt_self a ha]
  rw [he,map_mul,map_star]
  exact star_mul_self_nonneg (φ (CFC.sqrt a))
lemma unitary_lift_of_isUnit {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (a : A) (ha : IsUnit a) (u : unitary B)
    (he : φ a = (u : B)) : ∃ v : unitary A, φ (v : A) = (u : B) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hg : IsStrictlyPositive (star a*a) := ⟨star_mul_self_nonneg _,ha.star.mul ha⟩
  let r := (star a*a) ^ (-(1/2):ℝ)
  have hr : 0 ≤ r := CFC.rpow_nonneg
  have hrs : star r=r := (IsSelfAdjoint.of_nonneg hr).star_eq
  have hrunit : IsUnit r := hg.isUnit.cfcRpow _
  have hnorm : r*(star a*a)*r=1 := CFC.conjugate_rpow_neg_one_half _ hg
  have hv : a*r ∈ unitary A := (ha.mul hrunit).mem_unitary_of_star_mul_self (by
    rw [star_mul,hrs]
    calc r*star a*(a*r) = r*(star a*a)*r := by noncomm_ring
         _ = 1 := hnorm)
  have hφg : φ (star a*a)=1 := by rw [map_mul,map_star,he]; exact u.property.1
  have hφrnonneg : 0≤φ r := map_positive φ hr
  have hφr2 : (φ r)^2=1 := by
    have h := congrArg φ hnorm
    simpa only [map_mul,hφg,mul_one,map_one,pow_two] using h
  have hφr : φ r=1 := by
    calc
      φ r = CFC.sqrt ((φ r)^2) := (CFC.sqrt_sq (φ r) hφrnonneg).symm
      _ = 1 := by rw [hφr2,CFC.sqrt_one]
  exact ⟨⟨a*r,hv⟩,by change φ (a*r)=_; rw [map_mul,he,hφr,mul_one]⟩
lemma isUnit_of_two_grams {A : Type*} [CStarAlgebra A] (a : A)
    (hleft : IsUnit (star a*a)) (hright : IsUnit (a*star a)) : IsUnit a := by
  let l := Ring.inverse (star a*a)*star a
  let r := star a*Ring.inverse (a*star a)
  have hl : l*a=1 := by dsimp [l]; rw [mul_assoc,Ring.inverse_mul_cancel _ hleft]
  have hr : a*r=1 := by dsimp [r]; rw [← mul_assoc,Ring.mul_inverse_cancel _ hright]
  have he : l=r := by calc l=l*(a*r) := by rw [hr,mul_one]
                         _=(l*a)*r := (mul_assoc l a r).symm
                         _=r := by rw [hl,one_mul]
  exact ⟨⟨a,l,by rwa [he],hl⟩,rfl⟩


theorem unitary_lift {A : Type*} [CStarAlgebra A] (ω : Ultrafilter ℕ)
    (u : unitary (Algebra A ω)) :
    ∃ v : unitary (BoundedSeq A), quotientMap ω (v : BoundedSeq A) = (u : Algebra A ω) := by
  classical
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective (u : Algebra A ω)
  change quotientMap ω x=(u : Algebra A ω) at hx
  have hleft : star x*x-1 ∈ nullIdeal ω := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change quotientMap ω (star x*x-1)=0
    rw [map_sub,map_mul,map_star,map_one,hx,u.property.1,sub_self]
  have hright : x*star x-1 ∈ nullIdeal ω := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change quotientMap ω (x*star x-1)=0
    rw [map_sub,map_mul,map_star,map_one,hx,u.property.2,sub_self]
  have hl := (mem_nullIdeal ω _).mp hleft
  have hr := (mem_nullIdeal ω _).mp hright
  let good : ℕ → Prop := fun n => ‖star (x n)*x n-1‖ < 1/2 ∧ ‖x n*star (x n)-1‖ < 1/2
  have hg : ∀ᶠ n in (ω : Filter ℕ), good n := by
    exact (hl.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))).and
      (hr.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))
  let y : BoundedSeq A := ofNormedAddCommGroupDiscrete (fun n => if good n then x n else 1)
    (‖x‖+‖(1:A)‖) (fun n => by
      split_ifs
      · exact (x.norm_coe_le_norm n).trans (by linarith [norm_nonneg (1:A)])
      · exact by linarith [norm_nonneg x])
  have hxy : quotientMap ω y = quotientMap ω x := by
    apply Ideal.Quotient.eq.mpr
    apply (mem_nullIdeal ω _).mpr
    apply (tendsto_const_nhds (x := (0:ℝ))).congr'
    filter_upwards [hg] with n hn
    change (0:ℝ)=‖(if good n then x n else 1)-x n‖
    simp only [ite_eq_left hn,sub_self,norm_zero]
  have hnleft : ‖star y*y-1‖ ≤ (1/2 : ℝ) := by
    apply (BoundedContinuousFunction.norm_le (by norm_num)).mpr
    intro n
    change ‖star (if good n then x n else 1)*(if good n then x n else 1)-1‖ ≤ 1/2
    split_ifs with hn
    · exact hn.1.le
    · simp
  have hnright : ‖y*star y-1‖ ≤ (1/2 : ℝ) := by
    apply (BoundedContinuousFunction.norm_le (by norm_num)).mpr
    intro n
    change ‖(if good n then x n else 1)*star (if good n then x n else 1)-1‖ ≤ 1/2
    split_ifs with hn
    · exact hn.2.le
    · simp
  have hy : IsUnit y := by
    apply isUnit_of_two_grams
    · have h := isUnit_one_sub_of_norm_lt_one (x := 1-star y*y)
        (by rw [norm_sub_rev]; linarith)
      simpa only [sub_sub_cancel] using h
    · have h := isUnit_one_sub_of_norm_lt_one (x := 1-y*star y)
        (by rw [norm_sub_rev]; linarith)
      simpa only [sub_sub_cancel] using h
  exact unitary_lift_of_isUnit (quotientMap ω) y hy u (hxy.trans hx)
end KirchbergRordam.NormUltrapower
namespace KirchbergRordam.NormUltrapower
open Filter Topology BoundedContinuousFunction
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma eventually_norm_lt (ω : Ultrafilter ℕ) (x : BoundedSeq A) (c : ℝ)
    (h : ‖quotientMap ω x‖ < c) : ∀ᶠ n in (ω : Filter ℕ), ‖x n‖ < c := by
  change ‖Ideal.Quotient.mk (nullIdeal ω) x‖ < c at h
  rw [norm_mk_eq] at h
  exact (tendsto_norm ω x).eventually (gt_mem_nhds h)
end KirchbergRordam.NormUltrapower

namespace KirchbergRordam
open Filter
open scoped Topology CStarAlgebra
namespace Intertwining
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma tendsto_limitHom (φ : ℕ → A →⋆ₐ[ℂ] B)
    (hφ : ∀ a, CauchySeq (fun n => φ n a)) (a : A) :
    Tendsto (fun n => φ n a) atTop (𝓝 (limitHom φ hφ a)) :=
  (hφ a).tendsto_limUnder

end Intertwining


end KirchbergRordam
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Absorption
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

namespace KirchbergRordam
open Filter
open scoped Topology
namespace Intertwining
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
lemma dense_pointwise_cauchy (φ : ℕ → A →⋆ₐ[ℂ] B) (a : ℕ → A)
    (ha : DenseRange a) (hc : ∀ i, CauchySeq (fun n => φ n (a i))) :
    ∀ x, CauchySeq (fun n => φ n x) := by
  intro x
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨i,hi⟩ := Metric.denseRange_iff.mp ha x (ε/3) (by positivity)
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (hc i) (ε/3) (by positivity)
  refine ⟨N,fun m hm n hn => ?_⟩
  have hdist (k : ℕ) : dist (φ k x) (φ k (a i)) ≤ dist x (a i) := by
    rw [dist_eq_norm,dist_eq_norm,← map_sub]
    exact NonUnitalStarAlgHom.norm_apply_le (φ k) _
  have hd := dist_triangle4 (φ m x) (φ m (a i)) (φ n (a i)) (φ n x)
  have h1 := hdist m
  have h2 := hdist n
  have h3 := hN m hm n hn
  rw [dist_comm (φ n (a i)) (φ n x)] at hd
  have hi' : dist x (a i) < ε/3 := by simpa only [dist_comm] using hi
  linarith
lemma limitHom_isometry (φ : ℕ → A →⋆ₐ[ℂ] B)
    (hc : ∀ a, CauchySeq (fun n => φ n a)) (hi : ∀ n, Isometry (φ n)) :
    Isometry (limitHom φ hc) := by
  apply isometry_iff_dist_eq.mpr
  intro a b
  apply tendsto_nhds_unique ((tendsto_limitHom φ hc a).dist (tendsto_limitHom φ hc b))
  have he : (fun n => dist (φ n a) (φ n b)) = (fun _ : ℕ => dist a b) :=
    funext (fun n => (hi n).dist_eq a b)
  rw [he]
  exact tendsto_const_nhds
end Intertwining


theorem local_approximate_surjectivity {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ)
    (hlocal : ∀ (S : Finset A) (T : Finset B) (ε : ℝ), 0 < ε →
      ∃ β : B ≃⋆ₐ[ℂ] B,
        (∀ a ∈ S, dist (β (φ a)) (φ a) < ε) ∧
        (∀ b ∈ T, ∃ a : A, dist (β (φ a)) b < ε)) :
    Nonempty (A ≃⋆ₐ[ℂ] B) := by
  classical
  let a := TopologicalSpace.denseSeq A
  let b := TopologicalSpace.denseSeq B
  let e : ℕ → ℝ := fun n => (1/2 : ℝ)^n
  let State := (B ≃⋆ₐ[ℂ] B) × Finset A
  let Good : ℕ → State → State → Prop := fun n s t =>
    s.2 ⊆ t.2 ∧ a n ∈ t.2 ∧
    (∀ x ∈ s.2, dist (t.1 (φ x)) (s.1 (φ x)) < e n) ∧
    (∀ i ≤ n, ∃ x ∈ t.2, dist (t.1 (φ x)) (b i) < e n)
  have hex : ∀ n s, ∃ t, Good n s t := by
    intro n s
    let T : Finset B := (Finset.range (n+1)).image (fun i => s.1.symm (b i))
    obtain ⟨β,hfix,hdense⟩ := hlocal s.2 T (e n) (by dsimp [e]; positivity)
    have hw : ∀ i : Fin (n+1), ∃ x : A, dist (β (φ x)) (s.1.symm (b i)) < e n := by
      intro i
      apply hdense
      exact Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr i.isLt,rfl⟩
    choose w hw using hw
    refine ⟨(β.trans s.1, s.2 ∪ {a n} ∪ Finset.univ.image w), ?_⟩
    refine ⟨fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx),
      Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _)), ?_, ?_⟩
    · intro x hx
      change dist (s.1 (β (φ x))) (s.1 (φ x)) < _
      rw [(NonUnitalStarAlgHom.isometry s.1 s.1.injective).dist_eq]
      exact hfix x hx
    · intro i hi
      let j : Fin (n+1) := ⟨i,by omega⟩
      refine ⟨w j,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩),?_⟩
      change dist (s.1 (β (φ (w j)))) (b i) < _
      have hh := (NonUnitalStarAlgHom.isometry s.1 s.1.injective).dist_eq (β (φ (w j))) (s.1.symm (b i))
      rw [s.1.apply_symm_apply] at hh
      rw [hh]
      exact hw j
  let step : ℕ → State → State := fun n s => (hex n s).choose
  let state : ℕ → State := fun n => Nat.rec ((StarAlgEquiv.refl ℂ B), ∅)
    (fun k s => step k s) n
  have hstep : ∀ n, Good n (state n) (state (n+1)) := fun n => (hex n (state n)).choose_spec
  let S : ℕ → Finset A := fun n => (state n).2
  let Φ : ℕ → A →⋆ₐ[ℂ] B := fun n => (state n).1.toStarAlgHom.comp φ
  have hmono : Monotone S := monotone_nat_of_le_succ (fun n => (hstep n).1)
  have hfix : ∀ n x, x ∈ S n → dist (Φ (n+1) x) (Φ n x) < e n :=
    fun n x hx => (hstep n).2.2.1 x hx
  have hiso (n : ℕ) : Isometry (Φ n) :=
    (NonUnitalStarAlgHom.isometry (state n).1 (state n).1.injective).comp (NonUnitalStarAlgHom.isometry φ hφ)
  have hcS (k : ℕ) (x : A) (hx : x ∈ S k) :
      CauchySeq (fun n => Φ n x) := by
    apply (cauchySeq_shift k).mp
    apply cauchySeq_of_dist_le_of_summable (fun n => e (n+k))
    · intro n
      rw [dist_comm]
      simpa only [Nat.succ_add, Nat.add_succ] using (hfix (n+k) x (hmono (by omega) hx)).le
    · exact summable_geometric_two.comp_injective (add_left_injective k)
  have hc : ∀ x, CauchySeq (fun n => Φ n x) := by
    apply Intertwining.dense_pointwise_cauchy Φ a (TopologicalSpace.denseRange_denseSeq A)
    intro i
    exact hcS (i+1) (a i) (hstep i).2.1
  let f := Intertwining.limitHom Φ hc
  have hfi : Isometry f := Intertwining.limitHom_isometry Φ hc hiso
  have hdist (k : ℕ) (x : A) (hx : x ∈ S k) : dist (Φ k x) (f x) ≤ 2 * e k := by
    have ht := dist_le_tsum_of_dist_le_of_tendsto (fun n => e (n+k))
      (f := fun n => Φ (n+k) x)
      (fun n => by
        rw [dist_comm]
        simpa only [Nat.succ_add, Nat.add_succ] using (hfix (n+k) x (hmono (by omega) hx)).le)
      (summable_geometric_two.comp_injective (add_left_injective k))
      ((Intertwining.tendsto_limitHom Φ hc x).comp (tendsto_add_atTop_nat k)) 0
    simp only [zero_add] at ht
    have he : (∑' n, e (n+k)) = 2 * e k := by
      simp only [e,pow_add]
      rw [tsum_mul_right,tsum_geometric_two]
    exact ht.trans_eq he
  have hdense : DenseRange f := by
    have hsub : Set.range b ⊆ closure (Set.range f) := by
      intro y hy
      obtain ⟨i,rfl⟩ := hy
      apply Metric.mem_closure_iff.mpr
      intro ε hε
      have he0 : Tendsto (fun n => 2 * e n) atTop (𝓝 0) := by
        simpa only [mul_zero] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
            (by norm_num : (1/2 : ℝ)<1)).const_mul 2
      obtain ⟨N,hN⟩ := eventually_atTop.mp (he0.eventually (gt_mem_nhds hε))
      let n := max N i
      obtain ⟨x,hx,hxb⟩ := (hstep n).2.2.2 i (le_max_right _ _)
      refine ⟨f x,Set.mem_range_self x,?_⟩
      have htail := hdist (n+1) x hx
      have hen : 2 * e (n+1) = e n := by dsimp [e]; rw [pow_succ]; ring
      rw [hen] at htail
      have hbound := hN n (le_max_left _ _)
      have htri := dist_triangle (f x) (Φ (n+1) x) (b i)
      rw [dist_comm (f x) (Φ (n+1) x)] at htri
      change dist (Φ (n+1) x) (b i) < e n at hxb
      change dist (b i) (f x) < ε
      rw [dist_comm (b i) (f x)]
      linarith
    intro y
    apply closure_minimal hsub isClosed_closure
    exact TopologicalSpace.denseRange_denseSeq B y
  have hsurj : Function.Surjective f := by
    have hr : IsClosed (Set.range f) := hfi.isClosedEmbedding.isClosed_range
    exact fun y => by
      have hy := hdense y
      rw [hr.closure_eq] at hy
      exact hy
  exact ⟨StarAlgEquiv.ofBijective f ⟨hfi.injective,hsurj⟩⟩
end KirchbergRordam
namespace KirchbergRordam
section
open Filter Topology NormUltrapower



theorem inner_local_of_ultrapower_split_and_conjugacy
    {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (ω : Ultrafilter ℕ) (φ : A →⋆ₐ[ℂ] B)
    (ψ : B →⋆ₐ[ℂ] NormUltrapower.Algebra A ω)
    (hsplit : ∀ a, ψ (φ a) = NormUltrapower.diagonal ω a)
    (hconj : ∀ (T : Finset B) (ε : ℝ), 0 < ε →
      ∃ u : unitary (NormUltrapower.Algebra B ω), ∀ b ∈ T,
        dist (Unitary.conjStarAlgAut ℂ _ u (NormUltrapower.map φ ω (ψ b)))
          (NormUltrapower.diagonal ω b) < ε)
    (S : Finset A) (T : Finset B) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary B,
      (∀ a ∈ S, dist (Unitary.conjStarAlgAut ℂ _ u (φ a)) (φ a) < ε) ∧
      (∀ b ∈ T, ∃ a : A, dist (Unitary.conjStarAlgAut ℂ _ u (φ a)) b < ε) := by
  classical
  obtain ⟨u,hu⟩ := hconj (T ∪ S.image φ) ε hε
  obtain ⟨v,hv⟩ := unitary_lift ω u
  let w : ℕ → unitary B := fun n => ⟨(v : BoundedSeq B) n,
    ⟨congrArg (fun f : BoundedSeq B => f n) v.property.1,
      congrArg (fun f : BoundedSeq B => f n) v.property.2⟩⟩
  let β : ℕ → B ≃⋆ₐ[ℂ] B := fun n => Unitary.conjStarAlgAut ℂ B (w n)
  let x : B → BoundedSeq A := fun b => (Ideal.Quotient.mk_surjective (ψ b)).choose
  have hx (b : B) : quotientMap ω (x b) = ψ b :=
    (Ideal.Quotient.mk_surjective (ψ b)).choose_spec
  have hfix (a : A) (ha : a ∈ S) :
      ∀ᶠ n in (ω : Filter ℕ), dist (β n (φ a)) (φ a) < ε := by
    have h := hu (φ a) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩))
    rw [hsplit,map_diagonal] at h
    let z : BoundedSeq B := (v : BoundedSeq B)*constantSeq (φ a)*star (v : BoundedSeq B)-constantSeq (φ a)
    have hz : ‖quotientMap ω z‖ < ε := by
      simpa only [z,map_sub,map_mul,map_star,hv,NormUltrapower.diagonal,StarAlgHom.comp_apply,dist_eq_norm,
        Unitary.conjStarAlgAut_apply,Unitary.coe_star] using h
    simp only [dist_eq_norm]
    exact eventually_norm_lt ω z ε hz
  have hdense (b : B) (hb : b ∈ T) :
      ∀ᶠ n in (ω : Filter ℕ), dist (β n (φ (x b n))) b < ε := by
    have h := hu b (Finset.mem_union_left _ hb)
    let z : BoundedSeq B := (v : BoundedSeq B)*sequenceMap φ (x b)*star (v : BoundedSeq B)-constantSeq b
    have hmap : quotientMap ω (sequenceMap φ (x b))=NormUltrapower.map φ ω (ψ b) := by
      rw [← map_mk,hx]
    have hz : ‖quotientMap ω z‖ < ε := by
      simpa only [z,map_sub,map_mul,map_star,hv,hmap,NormUltrapower.diagonal,StarAlgHom.comp_apply,dist_eq_norm,
        Unitary.conjStarAlgAut_apply,Unitary.coe_star] using h
    simp only [dist_eq_norm]
    exact eventually_norm_lt ω z ε hz
  have hallS : ∀ᶠ n in (ω : Filter ℕ), ∀ a ∈ S, dist (β n (φ a)) (φ a) < ε :=
    S.eventually_all.mpr hfix
  have hallT : ∀ᶠ n in (ω : Filter ℕ), ∀ b ∈ T, dist (β n (φ (x b n))) b < ε :=
    T.eventually_all.mpr hdense
  obtain ⟨n,hnS,hnT⟩ := (hallS.and hallT).exists
  exact ⟨w n,hnS,fun b hb => ⟨x b n,hnT b hb⟩⟩
end

open Filter Topology


theorem local_approximate_surjectivity_of_dense_quotient
    {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace C]
    (φ : A →⋆ₐ[ℂ] B) (q : B →⋆ₐ[ℂ] C) (hq : DenseRange q)
    (hinj : Function.Injective (q.comp φ))
    (hlocal : ∀ (S : Finset A) (T : Finset B) (ε : ℝ), 0 < ε →
      ∃ u : unitary B,
        (∀ a ∈ S, dist (Unitary.conjStarAlgAut ℂ _ u (φ a)) (φ a) < ε) ∧
        (∀ b ∈ T, ∃ a : A, dist (Unitary.conjStarAlgAut ℂ _ u (φ a)) b < ε)) :
    Nonempty (A ≃⋆ₐ[ℂ] C) := by
  classical
  have hqdist (x y : B) : dist (q x) (q y) ≤ dist x y := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact NonUnitalStarAlgHom.norm_apply_le q (x-y)
  apply local_approximate_surjectivity (q.comp φ) hinj
  intro S T ε hε
  have he : 0 < ε/2 := half_pos hε
  choose b hb using fun t : C => hq.exists_dist_lt t he
  obtain ⟨u,hfix,happrox⟩ := hlocal S (T.image b) (ε/2) he
  let v : unitary C := ⟨q u, Unitary.map_mem q u.property⟩
  have hconj (x : B) :
      Unitary.conjStarAlgAut ℂ C v (q x) = q (Unitary.conjStarAlgAut ℂ B u x) := by
    simp only [Unitary.conjStarAlgAut_apply, map_mul, map_star]
    rfl
  refine ⟨Unitary.conjStarAlgAut ℂ C v, ?_, ?_⟩
  · intro a ha
    change dist (Unitary.conjStarAlgAut ℂ C v (q (φ a))) (q (φ a)) < ε
    rw [hconj]
    exact (hqdist _ _).trans_lt ((hfix a ha).trans (half_lt_self hε))
  · intro t ht
    obtain ⟨a,ha⟩ := happrox (b t) (Finset.mem_image.mpr ⟨t,ht,rfl⟩)
    refine ⟨a,?_⟩
    change dist (Unitary.conjStarAlgAut ℂ C v (q (φ a))) t < ε
    rw [hconj]
    have h1 := (hqdist (Unitary.conjStarAlgAut ℂ B u (φ a)) (b t)).trans_lt ha
    have h2 := hb t
    have htri := dist_triangle (q (Unitary.conjStarAlgAut ℂ B u (φ a))) (q (b t)) t
    rw [dist_comm (q (b t)) t] at htri
    linarith


theorem quotient_isomorphism_of_ultrapower_split_and_conjugacy_oai
    {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace C]
    (ω : Ultrafilter ℕ) (φ : A →⋆ₐ[ℂ] B)
    (q : B →⋆ₐ[ℂ] C) (hq : DenseRange q)
    (hinj : Function.Injective (q.comp φ))
    (ψ : B →⋆ₐ[ℂ] NormUltrapower.Algebra A ω)
    (hsplit : ∀ a, ψ (φ a) = NormUltrapower.diagonal ω a)
    (hconj : ∀ (T : Finset B) (ε : ℝ), 0 < ε →
      ∃ u : unitary (NormUltrapower.Algebra B ω), ∀ b ∈ T,
        dist (Unitary.conjStarAlgAut ℂ _ u (NormUltrapower.map φ ω (ψ b)))
          (NormUltrapower.diagonal ω b) < ε) :
    Nonempty (A ≃⋆ₐ[ℂ] C) :=
  local_approximate_surjectivity_of_dense_quotient φ q hq hinj
    (inner_local_of_ultrapower_split_and_conjugacy ω φ ψ hsplit hconj)
end KirchbergRordam

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KirchbergRordam.quotient_isomorphism_of_ultrapower_split_and_conjugacy_oai.{u_1, u_2, u_3} := @OAI.KirchbergRordam.quotient_isomorphism_of_ultrapower_split_and_conjugacy_oai.{u_1, u_2, u_3}
