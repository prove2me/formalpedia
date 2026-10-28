-- Prove2me | solution 1 for OAI.KirchbergRordam.character_criterion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T17:27:42.165775+00:00
-- url     : https://prove2.me/submissions/984c590e-eb08-4c6a-b8fc-e054b60fd7d6

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr013
import Definitions.Def_OAIB3Kr014
import Theorems.Thm_OAI_KirchbergRordam_PrimeDropPresentation_HalfFlip_finite_stage
import Theorems.Thm_OAI_KirchbergRordam_PrimeDropPresentation_central_no_character
import Theorems.Thm_OAI_KirchbergRordam_PrimeDropPresentation_stage_to_central
import Theorems.Thm_OAI_KirchbergRordam_spatial_absorption_of_central_maximal_half_flip

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


theorem mk_mem_central_iff (ω : Ultrafilter ℕ) (x : BoundedSeq A) :
    quotientMap ω x ∈ centralSubalgebra ω ↔
      ∀ a : A, Tendsto (fun n => ‖x n * a - a * x n‖) (ω : Filter ℕ) (𝓝 0) := by
  rw [mem_central_iff]
  constructor
  · intro h a
    have he : Ideal.Quotient.mk (nullIdeal ω) (x * constantSeq a) =
        Ideal.Quotient.mk (nullIdeal ω) (constantSeq a * x) := (h a).symm
    exact (mem_nullIdeal ω _).mp (Ideal.Quotient.eq.mp he)
  · intro h a
    have he : x * constantSeq a - constantSeq a * x ∈ nullIdeal ω :=
      (mem_nullIdeal ω _).mpr (h a)
    exact (Ideal.Quotient.eq.mpr he).symm

end NormUltrapower
end KirchbergRordam
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Reindexing
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

open Filter Topology
namespace KirchbergRordam.Reindex


theorem diagonal_select {ι : Type*} [Countable ι] (ω : Filter ℕ) [NeBot ω]
    (f : ι → ℕ → ℕ → ℝ)
    (hf : ∀ i s, Tendsto (f i s) ω (𝓝 0)) :
    ∃ k : ℕ → ℕ, ∀ i, Tendsto (fun s => f i s (k s)) atTop (𝓝 0) := by
  classical
  let := Encodable.ofCountable ι
  have good (s : ℕ) : ∃ l, ∀ i, Encodable.encode i ≤ s → |f i s l| < 1 / ((s:ℝ)+1) := by
    have hfin : {i : ι | Encodable.encode i ≤ s}.Finite :=
      (Set.finite_Iic s).preimage Encodable.encode_injective.injOn
    have he : ∀ᶠ l in ω, ∀ i ∈ {i : ι | Encodable.encode i ≤ s},
        |f i s l| < 1 / ((s:ℝ)+1) := hfin.eventually_all.mpr fun i _ => by
      have hp : (0:ℝ) < 1 / ((s:ℝ)+1) := by positivity
      simpa only [Real.dist_eq, sub_zero] using
        (tendsto_order.1 ((hf i s).abs)).2 _ (by simpa using hp)
    exact he.exists
  choose k hk using good
  refine ⟨k, fun i => ?_⟩
  apply squeeze_zero_norm' (a := fun s : ℕ => 1 / ((s:ℝ)+1))
  · filter_upwards [eventually_ge_atTop (Encodable.encode i)] with s hs
    simpa only [Real.norm_eq_abs] using (hk s i hs).le
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
end KirchbergRordam.Reindex

namespace KirchbergRordam.RationalDense
open Set Topology TopologicalSpace
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.KirchbergRordam.RationalDense.instAlgebraRat_solutions
lemma stage_countable {s : Set A} (hs : s.Countable) (n : ℕ) : (stage s n).Countable := by
  induction n with
  | zero => exact hs.union (Set.countable_range _)
  | succ n ih => exact ((ih.union ((ih.prod ih).image _)).union
      ((ih.prod ih).image _)).union (ih.image _)

lemma term_countable {s : Set A} (hs : s.Countable) : (termAlgebra s : Set A).Countable :=
  Set.countable_iUnion (stage_countable hs)
lemma subset_term (s : Set A) : s ⊆ termAlgebra s :=
  fun _ ha => mem_iUnion.mpr ⟨0,Or.inl ha⟩

theorem exists_countable_dense_star [SeparableSpace A] :
    ∃ S : StarSubalgebra ℚ A, (S : Set A).Countable ∧ Dense (S : Set A) ∧
      algebraMap ℂ A Complex.I ∈ S := by
  obtain ⟨s,hc,hd⟩ := exists_countable_dense A
  refine ⟨termAlgebra (insert (algebraMap ℂ A Complex.I) s),
    term_countable (hc.insert _), hd.mono ?_, subset_term _ (mem_insert _ _)⟩
  exact fun a ha => subset_term _ (mem_insert_of_mem _ ha)
end KirchbergRordam.RationalDense
open Topology
namespace KirchbergRordam.RationalDense
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]


attribute [local instance] OAI.KirchbergRordam.RationalDense.instAlgebraRat_solutions_1
theorem extend_complex (S : StarSubalgebra ℚ A) (hS : Dense (S : Set A))
    (f : S →+* B) (hf : UniformContinuous f)
    (hstar : ∀ x, f (star x) = star (f x))
    (hI : algebraMap ℂ A Complex.I ∈ S)
    (hfI : f ⟨algebraMap ℂ A Complex.I,hI⟩ = algebraMap ℂ B Complex.I) :
    ∃ g : A →⋆ₐ[ℂ] B, ∀ x : S, g x = f x := by
  let i : S →+* A := S.subtype.toRingHom
  have ui : IsUniformInducing i := isometry_subtype_coe.isUniformInducing
  have di : DenseRange i := hS.denseRange_val
  let g : A →+* B := IsDenseInducing.extendRingHom ui di hf
  have hg : Continuous g := (uniformContinuous_uniformly_extend ui di hf).continuous
  have he (x : S) : g x = f x :=
    IsDenseInducing.extend_eq (ui.isDenseInducing di) hf.continuous x
  have hs (x : A) : g (star x) = star (g x) := by
    refine di.induction_on x (p := fun x => g (star x) = star (g x))
      (isClosed_eq (hg.comp continuous_star) (continuous_star.comp hg)) ?_
    intro x
    change g (↑(star x) : A) = star (g (x : A))
    rw [he,he,hstar]
  have hgi : g (algebraMap ℂ A Complex.I) = algebraMap ℂ B Complex.I :=
    (he ⟨_,hI⟩).trans hfI
  have hr (r : ℝ) : g (algebraMap ℂ A (r:ℂ)) = algebraMap ℂ B (r:ℂ) := by
    refine (Rat.denseRange_cast (𝕜 := ℝ)).induction_on r
      (p := fun r => g (algebraMap ℂ A (r:ℂ)) = algebraMap ℂ B (r:ℂ))
      (isClosed_eq (hg.comp ((continuous_algebraMap ℂ A).comp Complex.continuous_ofReal))
        ((continuous_algebraMap ℂ B).comp Complex.continuous_ofReal)) ?_
    intro q
    change g (algebraMap ℂ A ((q : ℝ) : ℂ)) = algebraMap ℂ B ((q : ℝ) : ℂ)
    rw [Complex.ofReal_ratCast]
    exact g.map_rat_algebraMap q
  have hcomplex (z : ℂ) : g (algebraMap ℂ A z) = algebraMap ℂ B z := by
    conv_lhs => rw [← Complex.re_add_im z]
    simp only [map_add,map_mul,hr,hgi]
    rw [← map_mul, ← map_add, Complex.re_add_im]
  exact ⟨{ g with map_star' := hs, commutes' := hcomplex }, he⟩
end KirchbergRordam.RationalDense

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_CentralSequences
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
open Filter Topology
open Topology


namespace KirchbergRordam.NormUltrapower
open Filter Topology TopologicalSpace
open scoped CStarAlgebra
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

lemma exists_bounded_representative (ω : Ultrafilter ℕ) (x : Algebra A ω)
    {c : ℝ} (hc : ‖x‖ < c) :
    ∃ v : BoundedSeq A, quotientMap ω v = x ∧ ‖v‖ ≤ c := by
  obtain ⟨v,hv⟩ := Ideal.Quotient.mk_surjective x
  have hp : 0 ≤ c := (norm_nonneg x).trans hc.le
  refine ⟨cutRepresentative v c hp, ?_, cutRepresentative_norm_le v c hp⟩
  have hn : normLimit ω v < c := by rw [← norm_mk_eq, hv]; exact hc
  exact (cutRepresentative_mk_eq ω v c hp hn).symm.trans hv

namespace CollapseTest
variable {S : Type*} [Ring S] [StarRing S]

lemma natural {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]
    (j : S) (f : S → B) (ψ : B →⋆ₐ[ℂ] C) (i : CollapseTest S) :
    ψ (eval j f i) = eval j (fun x => ψ (f x)) i := by
  cases i <;> simp only [eval,map_add,map_mul,map_sub,map_one,map_star]
  exact congrArg (fun z => ψ (f j)-z) (ψ.commutes Complex.I)

lemma apply_seq {B : Type*} [CStarAlgebra B] (j : S) (f : S → BoundedSeq B)
    (i : CollapseTest S) (n : ℕ) :
    eval j f i n = eval j (fun x => f x n) i := by
  cases i <;> rfl
end CollapseTest


theorem countable_iterated_collapse {S : Type*} [Ring S] [StarRing S] [Countable S]
    [SeparableSpace A] (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (φ : S →+* Algebra (CentralAlgebra A ω) ω)
    (hφ : ∀ x, φ (star x) = star (φ x))
    (j : S) (hj : φ j = algebraMap ℂ (Algebra (CentralAlgebra A ω) ω) Complex.I) :
    ∃ θ : S →+* CentralAlgebra A ω,
      (∀ x, θ (star x) = star (θ x)) ∧
      (∀ x, ‖θ x‖ = ‖φ x‖) ∧
      θ j = algebraMap ℂ (CentralAlgebra A ω) Complex.I := by
  classical
  let F := CentralAlgebra A ω
  have hex (x : S) : ∃ u : BoundedSeq F, quotientMap ω u = φ x := Ideal.Quotient.mk_surjective _
  choose u hu using hex
  have hexi (x : S) (s : ℕ) : ∃ v : BoundedSeq A,
      quotientMap ω v = (u x s : Algebra A ω) ∧ ‖v‖ ≤ ‖u x‖+1 :=
    exists_bounded_representative ω _ ((u x).norm_coe_le_norm s |>.trans_lt (lt_add_one _))
  choose v hv hvnorm using hexi
  let a : ℕ → A := denseSeq A
  have ha : DenseRange a := denseRange_denseSeq A
  let test : (CollapseTest S ⊕ (S×ℕ)) → ℕ → ℕ → ℝ
    | .inl i, s, l => ‖CollapseTest.eval j (fun x => v x s) i l‖-
        ‖CollapseTest.eval j (fun x => u x s) i‖
    | .inr (x,n), s, l => ‖v x s l*a n-a n*v x s l‖
  have htcore (i : CollapseTest S) (s : ℕ) :
      Tendsto (test (.inl i) s) (ω : Filter ℕ) (𝓝 0) := by
    let z := CollapseTest.eval j (fun x => v x s) i
    have hz : quotientMap ω z =
        ((centralSubalgebra ω).subtype (CollapseTest.eval j (fun x => u x s) i)) := by
      rw [CollapseTest.natural,CollapseTest.natural]
      simp only [hv]
      rfl
    have hzNorm : normLimit ω z = ‖CollapseTest.eval j (fun x => u x s) i‖ := by
      rw [← norm_mk_eq]
      change ‖quotientMap ω z‖ = _
      rw [hz]
      rfl
    simpa only [test,hzNorm,sub_self] using
      (tendsto_norm ω z).sub_const ‖CollapseTest.eval j (fun x => u x s) i‖
  have ht (i : CollapseTest S ⊕ (S×ℕ)) (s : ℕ) :
      Tendsto (test i s) (ω : Filter ℕ) (𝓝 0) := by
    rcases i with i | ⟨x,n⟩
    · exact htcore i s
    · exact (mk_mem_central_iff ω (v x s)).mp (by rw [hv]; exact (u x s).property) (a n)
  obtain ⟨k,hk⟩ := Reindex.diagonal_select (ω : Filter ℕ) test ht
  have hfree : (ω : Filter ℕ) ≤ atTop := by simpa only [Nat.cofinite_eq_atTop] using hω
  have hk' (i) : Tendsto (fun s => test i s (k s)) (ω : Filter ℕ) (𝓝 0) :=
    (hk i).mono_left hfree
  let w : S → BoundedSeq A := fun x =>
    BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun s => v x s (k s)) (‖u x‖+1)
      (fun s => ((v x s).norm_coe_le_norm _).trans (hvnorm x s))
  let g : S → Algebra A ω := fun x => quotientMap ω (w x)
  have hgtest (i : CollapseTest S) : ‖CollapseTest.eval j g i‖ = ‖CollapseTest.eval j φ i‖ := by
    have hout : Tendsto (fun s => ‖CollapseTest.eval j (fun x => u x s) i‖)
        (ω : Filter ℕ) (𝓝 ‖CollapseTest.eval j φ i‖) := by
      have hz : quotientMap ω (CollapseTest.eval j u i) = CollapseTest.eval j φ i := by
        rw [CollapseTest.natural]
        simp only [hu]
      have hn : normLimit ω (CollapseTest.eval j u i) = ‖CollapseTest.eval j φ i‖ := by
        rw [← norm_mk_eq]
        exact congrArg norm hz
      simpa only [CollapseTest.apply_seq,hn] using tendsto_norm ω (CollapseTest.eval j u i)
    have htend : Tendsto (fun s => ‖CollapseTest.eval j w i s‖)
        (ω : Filter ℕ) (𝓝 ‖CollapseTest.eval j φ i‖) := by
      have h := (hk' (.inl i)).add hout
      simp only [zero_add] at h
      apply h.congr
      intro s
      simp only [test,sub_add_cancel,CollapseTest.apply_seq]
      rfl
    have hn : ‖CollapseTest.eval j g i‖ = normLimit ω (CollapseTest.eval j w i) := by
      rw [← CollapseTest.natural j w (quotientMap ω) i]
      exact norm_mk_eq ω _
    rw [hn]
    exact tendsto_nhds_unique (tendsto_norm ω _) htend
  have hadd (x y : S) : g (x+y)=g x+g y := by
    have h := hgtest (.add x y)
    simp only [CollapseTest.eval,map_add,sub_self,norm_zero,norm_eq_zero,sub_eq_zero] at h
    exact h
  have hmul (x y : S) : g (x*y)=g x*g y := by
    have h := hgtest (.mul x y)
    simp only [CollapseTest.eval,map_mul,sub_self,norm_zero,norm_eq_zero,sub_eq_zero] at h
    exact h
  have hstar (x : S) : g (star x)=star (g x) := by
    have h := hgtest (.adjoint x)
    simp only [CollapseTest.eval,hφ,sub_self,norm_zero,norm_eq_zero,sub_eq_zero] at h
    exact h
  have hzero : g 0=0 := by
    have h := hgtest .zero
    simpa only [CollapseTest.eval,map_zero,norm_zero,norm_eq_zero] using h
  have hone : g 1=1 := by
    have h := hgtest .one
    simpa only [CollapseTest.eval,map_one,sub_self,norm_zero,norm_eq_zero,sub_eq_zero] using h
  have hI : g j=algebraMap ℂ (Algebra A ω) Complex.I := by
    have h := hgtest .imag
    simpa only [CollapseTest.eval,hj,sub_self,norm_zero,norm_eq_zero,sub_eq_zero] using h
  have hgCentral (x : S) : g x ∈ centralSubalgebra ω := by
    rw [mem_central_iff]
    intro c
    refine ha.induction_on c (p:=fun c => diagonal ω c*g x=g x*diagonal ω c)
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro n
    have he := (quotient_eq_iff ω (w x*constantSeq (a n)) (constantSeq (a n)*w x)).mpr
      (hk' (.inr (x,n)))
    change quotientMap ω (constantSeq (a n))*quotientMap ω (w x)=
      quotientMap ω (w x)*quotientMap ω (constantSeq (a n))
    simpa only [map_mul] using he.symm
  let θ : S →+* CentralAlgebra A ω :=
    { toFun := fun x => ⟨g x,hgCentral x⟩
      map_zero' := Subtype.ext hzero
      map_one' := Subtype.ext hone
      map_add' := fun x y => Subtype.ext (hadd x y)
      map_mul' := fun x y => Subtype.ext (hmul x y) }
  exact ⟨θ,fun x => Subtype.ext (hstar x),fun x => hgtest (.value x),Subtype.ext hI⟩
end KirchbergRordam.NormUltrapower

namespace KirchbergRordam.NormUltrapower
open Filter Topology TopologicalSpace
open scoped CStarAlgebra


theorem iterated_central_collapse {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
    [SeparableSpace A] [SeparableSpace D]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (φ : D →⋆ₐ[ℂ] Algebra (CentralAlgebra A ω) ω) :
    ∃ θ : D →⋆ₐ[ℂ] CentralAlgebra A ω, ∀ x, ‖θ x‖ = ‖φ x‖ := by
  classical
  let : _root_.Algebra ℚ D := Algebra.compHom D (algebraMap ℚ ℂ)
  obtain ⟨S,hcount,hden,hI⟩ := RationalDense.exists_countable_dense_star (A:=D)
  let : Countable S := hcount.to_subtype
  let f : S →+* Algebra (CentralAlgebra A ω) ω := φ.toRingHom.comp S.subtype.toRingHom
  have hfstar (x : S) : f (star x)=star (f x) := map_star φ (x:D)
  have hfI : f ⟨_,hI⟩=algebraMap ℂ (Algebra (CentralAlgebra A ω) ω) Complex.I := φ.commutes _
  obtain ⟨g,hgs,hgn,hgi⟩ := countable_iterated_collapse ω hω f hfstar ⟨_,hI⟩ hfI
  have hbound (x : S) : ‖g x‖ ≤ ‖x‖ := by
    rw [hgn]
    exact NonUnitalStarAlgHom.norm_apply_le φ (x:D)
  have hLip : LipschitzWith 1 g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one,one_mul,dist_eq_norm,← map_sub]
    exact hbound (x-y)
  obtain ⟨θ,hθ⟩ := RationalDense.extend_complex S hden g hLip.uniformContinuous hgs hI hgi
  refine ⟨θ,fun x => ?_⟩
  refine hden.denseRange_val.induction_on x
    (p:=fun x => ‖θ x‖=‖φ x‖)
    (isClosed_eq (continuous_norm.comp (map_continuous θ)) (continuous_norm.comp (map_continuous φ))) ?_
  intro x
  rw [hθ]
  exact hgn x
end KirchbergRordam.NormUltrapower

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_InductiveLimit
attribute [-instance] _root_.OAI.KirchbergRordam.PrimeDropPresentation.instSeparableSpaceObjSystem _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
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


namespace KirchbergRordam.CStarInductiveLimit
section
universe u


attribute [instance] System.cstar


theorem of_isometry (S : System) (n : ℕ) : Isometry (of S n) := by
  apply AddMonoidHomClass.isometry_of_norm
  exact norm_of S n

instance instNontrivialAlgebraOfObjOfNatNat (S : System) [Nontrivial (S.obj 0)] : Nontrivial (Algebra S) :=
  (of_isometry S 0).injective.nontrivial


variable {C : Type*} [CStarAlgebra C]


theorem induction_on (S : System) {P : Algebra S → Prop} (x : Algebra S)
    (hclosed : IsClosed {x | P x}) (hof : ∀ n x, P (of S n x)) : P x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact hclosed
  | ih x =>
    refine DirectLimit.induction S.map ?_ x
    exact hof


theorem denseRange_of (S : System) :
    DenseRange (fun p : Σ n, S.obj n => of S p.1 p.2) := by
  intro x
  exact induction_on S x isClosed_closure
    (fun n x => subset_closure ⟨⟨n,x⟩,rfl⟩)


instance instSeparableSpaceAlgebraOfObj (S : System) [∀ n, TopologicalSpace.SeparableSpace (S.obj n)] :
    TopologicalSpace.SeparableSpace (Algebra S) :=
  (denseRange_of S).separableSpace (continuous_sigma fun n => map_continuous (of S n))

end

universe u


attribute [instance] Chain.cstar


end KirchbergRordam.CStarInductiveLimit


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_BalancedLimit
attribute [-instance] _root_.OAI.KirchbergRordam.PrimeDropPresentation.instSeparableSpaceObjSystem _root_.OAI.KirchbergRordam.PureStates.locallyConvexReal
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


namespace KirchbergRordam.CStarInductiveLimit
open Filter Topology
open scoped CStarAlgebra
variable {B : Type*} [CStarAlgebra B]


theorem exists_toCentral (S : System) [∀ n, TopologicalSpace.SeparableSpace (S.obj n)]
    {A : Type*} [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite)
    (φ : ∀ n, S.obj n →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra A ω) :
    Nonempty (Algebra S →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra A ω) := by
  have hfree : (ω : Filter ℕ) ≤ atTop := by simpa only [Nat.cofinite_eq_atTop] using hω
  obtain ⟨θ,_⟩ := NormUltrapower.iterated_central_collapse ω hω (toUltrapower S φ ω hfree)
  exact ⟨θ⟩
end KirchbergRordam.CStarInductiveLimit


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_DiagonalIteration
attribute [-instance] _root_.OAI.KirchbergRordam.PrimeDropPresentation.instSeparableSpaceObjSystem
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

namespace KirchbergRordam.DiagonalIteration
open scoped CStarAlgebra ComplexOrder
open Filter Topology
attribute [instance] System.cstar System.finite
end KirchbergRordam.DiagonalIteration


namespace KirchbergRordam.FiniteHalfFlipSequence
open scoped CStarAlgebra ComplexOrder
open Filter Topology
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma perturbation (φ ψ : A →⋆ₐ[ℂ] B) (u : unitary B) (x y : A) :
    ‖conj u (φ x)-ψ x‖ ≤ 2*‖x-y‖+‖conj u (φ y)-ψ y‖ := by
  have he : conj u (φ x)-ψ x =
      conj u (φ (x-y))+(conj u (φ y)-ψ y)-ψ (x-y) := by
    rw [map_sub,map_sub,map_sub]
    abel
  rw [he]
  have h1 : ‖conj u (φ (x-y))‖≤‖x-y‖ := by
    rw [StarAlgEquiv.norm_map]
    exact NonUnitalStarAlgHom.norm_apply_le φ _
  have h2 : ‖ψ (x-y)‖≤‖x-y‖ := NonUnitalStarAlgHom.norm_apply_le ψ _
  have h3 := norm_sub_le (conj u (φ (x-y))+(conj u (φ y)-ψ y)) (ψ (x-y))
  have h4 := norm_add_le (conj u (φ (x-y))) (conj u (φ y)-ψ y)
  linarith

theorem exists_sequence [TopologicalSpace.SeparableSpace A]
    (φ ψ : A →⋆ₐ[ℂ] B)
    (h : ∀ F : Finset A, ∀ ε : ℝ, 0<ε → ∃ u : unitary B,
      ∀ x∈F, ‖conj u (φ x)-ψ x‖≤ε) :
    ∃ u : ℕ → unitary B, ∀ x : A,
      Tendsto (fun n => conj (u n) (φ x)) atTop (𝓝 (ψ x)) := by
  classical
  let a := TopologicalSpace.denseSeq A
  have he (n : ℕ) : 0<(1:ℝ)/((n:ℝ)+1) := by positivity
  choose u hu using fun n : ℕ => h ((Finset.range (n+1)).image a) (1/((n:ℝ)+1)) (he n)
  refine ⟨u,fun x => ?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨i,hi⟩ := (TopologicalSpace.denseRange_denseSeq A).exists_dist_lt x (by positivity : 0<ε/4)
  have hp : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hp.eventually (gt_mem_nhds (by positivity : 0<ε/2)))
  refine ⟨max i N,fun n hn => ?_⟩
  have hin : i∈Finset.range (n+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le ((le_max_left i N).trans hn))
  have hb := hu n (a i) (Finset.mem_image_of_mem a hin)
  have hp' := perturbation φ ψ (u n) x (a i)
  rw [dist_eq_norm] at hi ⊢
  have hn' := hN n ((le_max_right i N).trans hn)
  have hx : ‖x-a i‖<ε/4 := by simpa only [a,norm_sub_rev] using hi
  linarith
end KirchbergRordam.FiniteHalfFlipSequence
namespace KirchbergRordam.CStarInductiveLimit
lemma approximation_common_stage (S : System) (F : Finset (Algebra S)) (ε : ℝ) (hε : 0<ε) :
    ∃ n : ℕ, ∃ a : Algebra S → S.obj n, ∀ x∈F, ‖of S n (a x)-x‖<ε := by
  classical
  choose v hv using fun x : Algebra S => (denseRange_of S).exists_dist_lt x hε
  let n := F.sup (fun x => (v x).1)
  let a : Algebra S → S.obj n := fun x => if hx : x∈F then
    S.map (v x).1 n (Finset.le_sup (f:=fun x => (v x).1) hx) (v x).2 else 0
  refine ⟨n,a,fun x hx => ?_⟩
  dsimp only [a]
  rw [dite_eq_left hx,of_map]
  simpa only [dist_eq_norm,norm_sub_rev] using hv x
end KirchbergRordam.CStarInductiveLimit
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
namespace KirchbergRordam.MinTensor
open scoped TensorProduct
universe u


attribute [instance] RepresentationPair.normH RepresentationPair.innerH
  RepresentationPair.completeH RepresentationPair.normK RepresentationPair.innerK
  RepresentationPair.completeK


end KirchbergRordam.MinTensor

namespace KirchbergRordam.MinTensor
open scoped TensorProduct CStarAlgebra
universe u
variable (A B : Type u) [CStarAlgebra A] [CStarAlgebra B]

variable {A B}
lemma denseRange_of : DenseRange (of (A := A) (B := B)) :=
  UniformSpace.Completion.denseRange_coe

end KirchbergRordam.MinTensor
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_InfiniteTensor
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

namespace KirchbergRordam.NormUltrapower
lemma map_central_of_equiv {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (e : X ≃⋆ₐ[ℂ] Y) (ω : Ultrafilter ℕ) (z : CentralAlgebra X ω) :
    map e.toStarAlgHom ω (z : Algebra X ω) ∈ centralSubalgebra ω := by
  apply (mem_central_iff ω _).mpr
  intro b
  let a := e.symm b
  have h := congrArg (map e.toStarAlgHom ω)
    ((mem_central_iff ω (z : Algebra X ω)).mp z.property a)
  simpa only [map_mul,map_diagonal,StarAlgEquiv.toStarAlgHom_apply, a, e.apply_symm_apply] using h
lemma map_equiv_inverse {X Y : Type*} [CStarAlgebra X] [CStarAlgebra Y]
    (e : X ≃⋆ₐ[ℂ] Y) (ω : Ultrafilter ℕ) (x : Algebra X ω) :
    map e.symm.toStarAlgHom ω (map e.toStarAlgHom ω x)=x := by
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective x
  change quotientMap ω (sequenceMap e.symm.toStarAlgHom (sequenceMap e.toStarAlgHom y))=quotientMap ω y
  congr 1
  ext n
  exact e.symm_apply_apply (y n)
end KirchbergRordam.NormUltrapower
namespace KirchbergRordam
section
open NormUltrapower


theorem central_isomorphism {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (θ : A ≃⋆ₐ[ℂ] B) (ω : Ultrafilter ℕ) :
    Nonempty (CentralAlgebra A ω ≃⋆ₐ[ℂ] CentralAlgebra B ω) := by
  let f : CentralAlgebra A ω →⋆ₐ[ℂ] CentralAlgebra B ω :=
    StarAlgHom.codRestrict ((NormUltrapower.map θ.toStarAlgHom ω).comp (centralSubalgebra ω).subtype)
      (centralSubalgebra ω) (map_central_of_equiv θ ω)
  let g : CentralAlgebra B ω →⋆ₐ[ℂ] CentralAlgebra A ω :=
    StarAlgHom.codRestrict ((NormUltrapower.map θ.symm.toStarAlgHom ω).comp (centralSubalgebra ω).subtype)
      (centralSubalgebra ω) (map_central_of_equiv θ.symm ω)
  have hgf : Function.LeftInverse g f := by
    intro z
    apply Subtype.ext
    exact map_equiv_inverse θ ω (z : NormUltrapower.Algebra A ω)
  have hfg : Function.RightInverse g f := by
    intro z
    apply Subtype.ext
    exact map_equiv_inverse θ.symm ω (z : NormUltrapower.Algebra B ω)
  exact ⟨StarAlgEquiv.ofBijective f ⟨hgf.injective,hfg.surjective⟩⟩
end
open NormUltrapower
open scoped TensorProduct
universe uTensor


theorem minimal_tensor_central_right (A D : Type uTensor) [CStarAlgebra A] [CStarAlgebra D]
    (ω : Ultrafilter ℕ) :
    Nonempty (CentralAlgebra D ω →⋆ₐ[ℂ] CentralAlgebra (MinTensor.Algebra A D) ω) := by
  let B := MinTensor.Algebra A D
  let l : A →⋆ₐ[ℂ] B := MinTensor.includeLeft
  let r : D →⋆ₐ[ℂ] B := MinTensor.includeRight
  let f : CentralAlgebra D ω →⋆ₐ[ℂ] NormUltrapower.Algebra B ω :=
    (NormUltrapower.map r ω).comp (centralSubalgebra ω).subtype
  have hcentral (z : CentralAlgebra D ω) : f z ∈ centralSubalgebra ω := by
    have hl (a : A) : Commute (diagonal ω (l a)) (f z) := by
      obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective (z : NormUltrapower.Algebra D ω)
      change quotientMap ω x=(z : NormUltrapower.Algebra D ω) at hx
      change Commute (diagonal ω (l a)) (NormUltrapower.map r ω (z : NormUltrapower.Algebra D ω))
      rw [← hx,map_mk]
      change quotientMap ω (constantSeq (l a))*quotientMap ω (sequenceMap r x)=
        quotientMap ω (sequenceMap r x)*quotientMap ω (constantSeq (l a))
      rw [← map_mul,← map_mul]
      congr 1
      ext n
      exact (MinTensor.legs_commute a (x n)).eq
    have hr (d : D) : Commute (diagonal ω (r d)) (f z) := by
      have hz := (mem_central_iff ω (z : NormUltrapower.Algebra D ω)).mp z.property d
      have he := congrArg (NormUltrapower.map r ω) hz
      change diagonal ω (r d) * NormUltrapower.map r ω (z : NormUltrapower.Algebra D ω) =
        NormUltrapower.map r ω (z : NormUltrapower.Algebra D ω) * diagonal ω (r d)
      simpa only [map_mul,map_diagonal] using he
    apply (mem_central_iff ω (f z)).mpr
    intro b
    have hclosed : IsClosed {b : B | diagonal ω b*f z=f z*diagonal ω b} :=
      isClosed_eq (((diagonal_isometry (A := B) ω).continuous).mul continuous_const)
        (continuous_const.mul ((diagonal_isometry (A := B) ω).continuous))
    apply (hclosed.closure_subset_iff (s := Set.range (MinTensor.of (A := A) (B := D)))).mpr ?_
      (MinTensor.denseRange_of b)
    rintro b ⟨x,rfl⟩
    obtain ⟨y,rfl⟩ := MinTensor.rawEquiv.surjective x
    change diagonal ω (MinTensor.of (MinTensor.rawEquiv y)) * f z =
      f z * diagonal ω (MinTensor.of (MinTensor.rawEquiv y))
    induction y using OAI.tensorInductionOn with
    | tmul a d =>
      have he : MinTensor.of (MinTensor.rawEquiv (a ⊗ₜ[ℂ] d))=l a*r d := by
        change MinTensor.of (MinTensor.rawEquiv (a ⊗ₜ[ℂ] d))=
          MinTensor.of (MinTensor.rawEquiv (a ⊗ₜ[ℂ] (1:D))) *
            MinTensor.of (MinTensor.rawEquiv ((1:A) ⊗ₜ[ℂ] d))
        rw [← map_mul,← map_mul]
        simp only [_root_.Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
      rw [he,map_mul]
      exact ((hl a).mul_left (hr d)).eq
    | add x y hx hy =>
      simp only [map_add,add_mul,mul_add]
      rw [hx,hy]
  exact ⟨StarAlgHom.codRestrict f (centralSubalgebra ω) hcentral⟩
end KirchbergRordam
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimePresentation
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

namespace KirchbergRordam.PrimeDropPresentation
open scoped CStarAlgebra ComplexOrder
variable (S : PrimeDropPresentation)
lemma size_two (n : ℕ) : 2≤S.size n := by
  rw [S.size_power]
  exact Nat.le_self_pow (by omega) 2
instance instNeZeroNatSize (n : ℕ) : NeZero (S.size n) := ⟨by have := S.size_two n; omega⟩
instance instNontrivialStage (n : ℕ) : Nontrivial (S.Stage n) := inferInstanceAs
  (Nontrivial (PrimeDimensionDrop.Algebra (S.size n) (S.size n+1)))

instance instNontrivialObjSystem (n : ℕ) : Nontrivial (S.system.obj n) := inferInstanceAs (Nontrivial (S.Stage n))
instance instNontrivialAlgebra : Nontrivial S.Algebra := inferInstanceAs (Nontrivial (CStarInductiveLimit.Algebra S.system))
instance instSeparableSpaceAlgebra : TopologicalSpace.SeparableSpace S.Algebra := inferInstanceAs (TopologicalSpace.SeparableSpace (CStarInductiveLimit.Algebra S.system))
theorem to_central (A : Type*) [CStarAlgebra A] [Nontrivial A]
    [TopologicalSpace.SeparableSpace A] (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤Filter.cofinite)
    (hF : IsEmpty (NormUltrapower.CentralAlgebra A ω →⋆ₐ[ℂ] ℂ)) :
    Nonempty (S.Algebra →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra A ω) :=
  CStarInductiveLimit.exists_toCentral S.system ω hω (fun n => (S.stage_to_central A ω hω hF n).some)
end KirchbergRordam.PrimeDropPresentation
namespace KirchbergRordam.PrimeDropPresentation.HalfFlip
open scoped CStarAlgebra ComplexOrder
open Filter Topology
open PrimeDropPresentation.Iteration
open UnitaryDisplacement BalancedDropHalfFlip
variable (S : PrimeDropPresentation)

lemma common_stage (F : Finset S.Algebra) (ε : ℝ) (hε : 0<ε) :
    ∃ n : ℕ, ∃ a : S.Algebra → S.Stage n, ∀ x∈F, ‖S.inclusion n (a x)-x‖<ε :=
  CStarInductiveLimit.approximation_common_stage S.system F ε hε

lemma finite_control (F : Finset S.Algebra) (ε : ℝ) (hε : 0<ε) :
    ∃ w : unitary (MaxTensor.Algebra S.Algebra S.Algebra), ∀ x∈F,
      ‖conj w (MaxTensor.includeLeft x)-MaxTensor.includeRight x‖≤ε := by
  classical
  obtain ⟨n,a,ha⟩ := common_stage S F (ε/4) (by positivity)
  obtain ⟨w,hw⟩ := finite_stage S n (F.image a) (ε/2) (by positivity)
  refine ⟨w,fun x hx => ?_⟩
  have hb := hw (a x) (Finset.mem_image_of_mem a hx)
  have hc := FiniteHalfFlipSequence.perturbation MaxTensor.includeLeft MaxTensor.includeRight w x (S.inclusion n (a x))
  have hd := ha x hx
  rw [norm_sub_rev] at hd
  change ‖conj w (MaxTensor.includeLeft x)-MaxTensor.includeRight x‖≤
    2*‖x-S.inclusion n (a x)‖+‖conj w (MaxTensor.includeLeft (S.inclusion n (a x)))-MaxTensor.includeRight (S.inclusion n (a x))‖ at hc
  linarith


theorem exists_half_flip : ∃ w : ℕ → unitary (MaxTensor.Algebra S.Algebra S.Algebra),
    ∀ x : S.Algebra, Tendsto (fun n => conj (w n) (MaxTensor.includeLeft x)) atTop
      (𝓝 (MaxTensor.includeRight x)) :=
  FiniteHalfFlipSequence.exists_sequence MaxTensor.includeLeft MaxTensor.includeRight (finite_control S)
end KirchbergRordam.PrimeDropPresentation.HalfFlip
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimeChannels
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

namespace KirchbergRordam.PrimeDropPresentation
open Filter
variable (S : PrimeDropPresentation)


theorem character_criterion
    (A : Type) [CStarAlgebra A] [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤cofinite) :
    IsEmpty (NormUltrapower.CentralAlgebra A ω →⋆ₐ[ℂ] ℂ) ↔
      Nonempty (A ≃⋆ₐ[ℂ] MinTensor.Algebra A S.Algebra) := by
  constructor
  · intro hF
    obtain ⟨ι⟩ := S.to_central A ω hω hF
    obtain ⟨u,hu⟩ := HalfFlip.exists_half_flip S
    exact spatial_absorption_of_central_maximal_half_flip A S.Algebra ω ι u hu
  · rintro ⟨θ⟩
    obtain ⟨e⟩ := central_isomorphism θ ω
    obtain ⟨r⟩ := minimal_tensor_central_right A S.Algebra ω
    have hF := S.central_no_character ω hω
    exact ⟨fun χ => hF.false ((χ.comp e.symm.toStarAlgHom).comp r)⟩


end KirchbergRordam.PrimeDropPresentation
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_JiangSu
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


namespace KirchbergRordam.JiangSu


instance instNontrivialAlgebra : Nontrivial Algebra := inferInstanceAs
  (Nontrivial (CStarInductiveLimit.Algebra StandardPrimeModel.presentation.system))
instance instSeparableSpaceAlgebra : TopologicalSpace.SeparableSpace Algebra := inferInstanceAs
  (TopologicalSpace.SeparableSpace (CStarInductiveLimit.Algebra StandardPrimeModel.presentation.system))

open StandardPrimeMultiplicity

end KirchbergRordam.JiangSu

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KirchbergRordam


lemma hasNoCharacters_iff (A : Type*) [CStarAlgebra A] :
    HasNoCharacters A ↔ IsEmpty (A →⋆ₐ[ℂ] ℂ) := by
  classical
  constructor
  · intro h
    refine ⟨fun χ => ?_⟩
    have he := DFunLike.congr_fun (h χ.toNonUnitalStarAlgHom) 1
    change χ 1=0 at he
    rw [map_one] at he
    exact one_ne_zero he
  · intro h χ
    by_contra hn
    exact h.false (unitalCharacter χ hn)
attribute [local instance 1100] StarCompletion.completionStar

theorem character_criterion_oai
    (A : Type) [CStarAlgebra A] [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤Filter.cofinite) :
    HasNoCharacters (NormUltrapower.CentralAlgebra A ω) ↔
      Nonempty (A ≃⋆ₐ[ℂ] MinTensor.Algebra A JiangSu.Algebra) := by
  rw [hasNoCharacters_iff]
  exact StandardPrimeModel.presentation.character_criterion A ω hω
end KirchbergRordam
end

end OAI
end

theorem solution : type_of% @OAI.KirchbergRordam.character_criterion_oai := @OAI.KirchbergRordam.character_criterion_oai
