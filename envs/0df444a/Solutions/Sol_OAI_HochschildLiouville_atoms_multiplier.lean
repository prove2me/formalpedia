-- Prove2me | solution 1 for OAI.HochschildLiouville.atoms_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:52:16.34632+00:00
-- url     : https://prove2.me/submissions/7357a807-82b5-4ba1-969c-3e577826209b

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_HochschildFirstLetter_countable_first_letter_rigidity

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section

namespace HochschildRigidity
open Finset

section FourierWindows
variable {L : ℕ} [NeZero L]

end FourierWindows

section TraceHilbertSpace
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ)

lemma preGNS_norm_star (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a : A) :
    ‖τ.toPreGNS (star a)‖ = ‖τ.toPreGNS a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  push_cast
  simp only [τ.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS, star_star]
  exact htr _ _
lemma preGNS_norm_mul_right_le (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a b : A) :
    ‖τ.toPreGNS (a * b)‖ ≤ ‖b‖ * ‖τ.toPreGNS a‖ := by
  rw [← preGNS_norm_star τ htr, star_mul]
  exact (preGNS_norm_mul_le τ (star b) (star a)).trans_eq
    (by rw [norm_star, preGNS_norm_star τ htr])
end TraceHilbertSpace
end HochschildRigidity
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric

namespace HochschildCStarQuotient
variable {A : Type*} [CStarAlgebra A]

class StarClosed (I : Ideal A) : Prop where
  star_mem {x : A} : x ∈ I → star x ∈ I

variable (I : Ideal A) [I.IsTwoSided]

lemma norm_mk_le (x : A) : ‖Ideal.Quotient.mk I x‖ ≤ ‖x‖ :=
  Submodule.Quotient.norm_mk_le I x

lemma norm_mk_lt (x : A ⧸ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, Ideal.Quotient.mk I a = x ∧ ‖a‖ < ‖x‖ + ε :=
  QuotientAddGroup.exists_norm_mk_lt x hε

instance quotientSeminormedRing : SeminormedRing (A ⧸ I) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε => by
    have := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, Metric.mem_ball, and_imp, Prod.forall, Prod.exists] at this
    rcases this with ⟨ε₁, ε₂, ⟨h₁, h₂⟩, h⟩
    obtain ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩ := norm_mk_lt I x h₁, norm_mk_lt I y h₂
    simp only [dist, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [norm_mk_le I a]⟩
      ⟨by linarith, by linarith [norm_mk_le I b]⟩
    calc
      _ ≤ ‖a‖ * ‖b‖ := (norm_mk_le I (a*b)).trans (norm_mul_le a b)
      _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le

instance quotientNormedRing [IsClosed (I : Set A)] : NormedRing (A ⧸ I) :=
  { quotientSeminormedRing I, Submodule.Quotient.normedAddCommGroup I with }

instance quotientNormedAlgebra : NormedAlgebra ℂ (A ⧸ I) :=
  { Submodule.Quotient.normedSpace I ℂ, Ideal.Quotient.algebra ℂ with }

variable [StarClosed I]

instance quotientStar : Star (A ⧸ I) where
  star := Quotient.map' star fun a b hab => by
    rw [Submodule.quotientRel_def] at hab ⊢
    simpa only [star_sub] using StarClosed.star_mem (I := I) hab

@[simp] lemma star_mk (a : A) : star (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (star a) := rfl

instance quotientStarRing : StarRing (A ⧸ I) where
  star_involutive x := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    simp
  star_mul x y := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [← map_mul, star_mk, star_mul]
  star_add x y := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [← map_add, star_mk, star_add]

instance quotientStarModule : StarModule ℂ (A ⧸ I) where
  star_smul r x := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk I (star (r • a)) = Ideal.Quotient.mk I (star r • star a)
    rw [star_smul]

lemma norm_star_le (x : A ⧸ I) : ‖star x‖ ≤ ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a,rfl,ha⟩ := norm_mk_lt I x hε
  exact (norm_mk_le I (star a)).trans (by simpa only [norm_star] using ha.le)

instance quotientNormedStarGroup : NormedStarGroup (A ⧸ I) where
  norm_star_le := norm_star_le I

def starSubalgebra : NonUnitalStarSubalgebra ℂ A where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  mul_mem' := fun _ hy => I.mul_mem_left _ hy
  smul_mem' := fun r x hx => by
    change r • x ∈ I
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ hx
  star_mem' := StarClosed.star_mem

instance starSubalgebra_closed [h : IsClosed (I : Set A)] :
    IsClosed (starSubalgebra I : Set A) := h

omit [I.IsTwoSided] in

lemma exists_cut [IsClosed (I : Set A)] (b : A) (hb : b ∈ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : A, e ∈ I ∧ star e = e ∧ ‖1-e‖ ≤ 1 ∧ ‖b-b*e‖ < ε := by
  let oa := CStarAlgebra.spectralOrder A
  let osa := CStarAlgebra.spectralOrderedRing A
  let S := starSubalgebra I
  let os := CStarAlgebra.spectralOrder S
  let oss := CStarAlgebra.spectralOrderedRing S
  let b' : S := ⟨b,hb⟩
  have hi := CStarAlgebra.increasingApproximateUnit S
  have hd : ∀ᶠ e : S in CStarAlgebra.approximateUnit S, ‖b'-b'*e‖ < ε := by
    have ht := ((tendsto_const_nhds (x := b')).sub (hi.tendsto_mul_left b')).norm
    simpa only [sub_self, norm_zero] using ht.eventually (gt_mem_nhds (by simpa only [sub_self, norm_zero] using hε))
  obtain ⟨e,he₀,he₁,he₂⟩ := (hi.eventually_nonneg.and (hi.eventually_norm.and hd)).exists
  have hepos : 0 ≤ (e:A) := by
    simpa using (@NonUnitalStarRingHom.map_le_map_of_map_star S A _ os _ oss _ oa _ osa
      (NonUnitalStarRingHomClass.toNonUnitalStarRingHom (NonUnitalStarSubalgebraClass.subtype S)) 0 e he₀)
  have henorm : ‖(e:A)‖ ≤ 1 := he₁
  have heone : (e:A) ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hepos).mp henorm
  refine ⟨e,e.property,hepos.isSelfAdjoint.star_eq,?_,he₂⟩
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg (1-(e:A)) (sub_nonneg.mpr heone)).mpr
    (sub_le_self _ hepos)

lemma quotient_cstar [IsClosed (I : Set A)] (x : A ⧸ I) :
    ‖x‖ * ‖x‖ ≤ ‖star x*x‖ := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [star_mk, ← map_mul]
  apply QuotientAddGroup.le_norm_iff.mpr
  intro t ht
  apply le_of_forall_pos_le_add
  intro ε hε
  have hb : t-star a*a ∈ I := (Ideal.Quotient.eq).mp ht
  obtain ⟨e,he,hes,hen,heb⟩ := exists_cut I (t-star a*a) hb hε
  have hqe : Ideal.Quotient.mk I e = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr he
  have hx : Ideal.Quotient.mk I (a*(1-e)) = Ideal.Quotient.mk I a := by
    simp only [map_mul,map_sub,map_one,hqe,sub_zero,mul_one]
  calc
    ‖Ideal.Quotient.mk I a‖ * ‖Ideal.Quotient.mk I a‖ ≤ ‖a*(1-e)‖ * ‖a*(1-e)‖ := by
      apply mul_self_le_mul_self (norm_nonneg _)
      rw [← hx]
      exact norm_mk_le I _
    _ = ‖(1-e)*(star a*a)*(1-e)‖ := by
      rw [← CStarRing.norm_star_mul_self]
      simp only [star_mul,star_sub,star_one,hes,mul_assoc]
    _ = ‖(1-e)*t*(1-e)-(1-e)*((t-star a*a)-(t-star a*a)*e)‖ := by
      congr 1
      noncomm_ring
    _ ≤ ‖(1-e)*t*(1-e)‖ + ‖(1-e)*((t-star a*a)-(t-star a*a)*e)‖ := norm_sub_le _ _
    _ ≤ ‖t‖ + ε := by
      apply add_le_add
      · calc
          _ ≤ ‖1-e‖*‖t‖*‖1-e‖ := (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ 1*‖t‖*1 := by gcongr
          _ = _ := by ring
      · calc
          _ ≤ ‖1-e‖*‖(t-star a*a)-(t-star a*a)*e‖ := norm_mul_le _ _
          _ ≤ 1*‖(t-star a*a)-(t-star a*a)*e‖ :=
            mul_le_mul_of_nonneg_right hen (norm_nonneg _)
          _ ≤ ε := by simpa using heb.le

instance quotientCStarAlgebra [IsClosed (I : Set A)] : CStarAlgebra (A ⧸ I) where
  norm_mul_self_le := quotient_cstar I
end HochschildCStarQuotient
end
end OAI
end

section
namespace OAI

noncomputable section

namespace TracialUltrapower
noncomputable section
open Filter
open scoped Topology BoundedContinuousFunction

section Modulus
variable {A E : Type*} [SeminormedAddCommGroup A] [SeminormedAddCommGroup E]

theorem ballSequential_iff_modulus (q : A → E) (R : A → A) :
    BallSequential q R ↔ BallModulus q R := by
  constructor
  · intro hs r ε hε
    by_contra h
    push Not at h
    choose x hx hxq hRx using fun j : ℕ =>
      h (1 / ((j : ℝ) + 1)) (by positivity)
    have hlim : Tendsto (fun j => ‖q (x j)‖) atTop (𝓝 0) :=
      squeeze_zero (fun _ => norm_nonneg _) (fun j => (hxq j).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hout := (hs x ⟨r, hx⟩ hlim).eventually_lt_const hε
    obtain ⟨j, hj⟩ := hout.exists
    exact (not_lt_of_ge (hRx j)) hj
  · intro hm x hx hlim
    obtain ⟨r, hr⟩ := hx
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := hm r ε hε
    filter_upwards [hlim.eventually_lt_const hδ] with j hj
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_norm] using hmod (x j) (hr j) hj

theorem BallModulus.map_tendsto {q : A → E} {R : A → A} (h : BallModulus q R)
    {ι : Type*} {l : Filter ι} {x : ι → A} {r : ℝ}
    (hx : ∀ᶠ j in l, ‖x j‖ ≤ r)
    (hlim : Tendsto (fun j => ‖q (x j)‖) l (𝓝 0)) :
    Tendsto (fun j => ‖q (R (x j))‖) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := h r ε hε
  filter_upwards [hx, hlim.eventually_lt_const hδ] with j hj hjq
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_norm] using hmod (x j) hj hjq

end Modulus

section NullSubmodule
variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]
variable (q : A →ₗ[ℂ] E) (ω : Filter ℕ)

def nullSubmodule : Submodule ℂ (ℕ →ᵇ A) where
  carrier := {x | Tendsto (fun j => q (x j)) ω (𝓝 0)}
  zero_mem' := by simpa using tendsto_const_nhds (x := (0 : E))
  add_mem' := by
    intro x y hx hy
    simpa only [Set.mem_ofPred_eq, BoundedContinuousFunction.add_apply, map_add, add_zero] using hx.add hy
  smul_mem' := by
    intro c x hx
    simpa only [Set.mem_ofPred_eq, BoundedContinuousFunction.smul_apply, map_smul, smul_zero] using hx.const_smul c

@[simp] theorem mem_nullSubmodule (x : ℕ →ᵇ A) :
    x ∈ nullSubmodule q ω ↔ Tendsto (fun j => ‖q (x j)‖) ω (𝓝 0) := by
  change Tendsto (fun j => q (x j)) ω (𝓝 0) ↔ _
  exact tendsto_zero_iff_norm_tendsto_zero

theorem nullSubmodule_map_invariant (R : A →L[ℂ] A) (hR : BallModulus q R) :
    nullSubmodule q ω ≤ (nullSubmodule q ω).comap
      (R.compLeftContinuousBounded ℕ).toLinearMap := by
  intro x hx
  rw [Submodule.mem_comap, mem_nullSubmodule]
  exact hR.map_tendsto (Eventually.of_forall x.norm_coe_le_norm)
    ((mem_nullSubmodule q ω x).mp hx)

def quotientMap (R : A →L[ℂ] A) (hR : BallModulus q R) :
    ((ℕ →ᵇ A) ⧸ nullSubmodule q ω) →ₗ[ℂ]
      ((ℕ →ᵇ A) ⧸ nullSubmodule q ω) :=
  (nullSubmodule q ω).mapQ (nullSubmodule q ω)
    (R.compLeftContinuousBounded ℕ).toLinearMap (nullSubmodule_map_invariant q ω R hR)

@[simp] theorem quotientMap_mk (R : A →L[ℂ] A) (hR : BallModulus q R)
    (x : ℕ →ᵇ A) :
    quotientMap q ω R hR (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (R.compLeftContinuousBounded ℕ x) := rfl

theorem norm_quotientMap_le (R : A →L[ℂ] A) (hR : BallModulus q R)
    (X : (ℕ →ᵇ A) ⧸ nullSubmodule q ω) :
    ‖quotientMap q ω R hR X‖ ≤ ‖R‖ * ‖X‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc : 0 < ‖R‖ + 1 := by positivity
  obtain ⟨x, rfl, hx⟩ := Submodule.Quotient.norm_mk_lt X (div_pos hε hc)
  rw [quotientMap_mk]
  have hcomp : ‖R.compLeftContinuousBounded ℕ x‖ ≤ ‖R‖ * ‖x‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro j
    exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left (x.norm_coe_le_norm j)
      (norm_nonneg _))
  calc
    _ ≤ ‖R.compLeftContinuousBounded ℕ x‖ := Submodule.Quotient.norm_mk_le _ _
    _ ≤ ‖R‖ * ‖x‖ := hcomp
    _ ≤ ‖R‖ * (‖(Submodule.Quotient.mk x : (ℕ →ᵇ A) ⧸ nullSubmodule q ω)‖ +
        ε / (‖R‖ + 1)) := by gcongr
    _ ≤ _ := by
      have hδ : 0 ≤ ε / (‖R‖ + 1) := (div_pos hε hc).le
      have heq : (‖R‖ + 1) * (ε / (‖R‖ + 1)) = ε := by field_simp
      nlinarith

def quotientContinuousMap (R : A →L[ℂ] A) (hR : BallModulus q R) :
    ((ℕ →ᵇ A) ⧸ nullSubmodule q ω) →L[ℂ]
      ((ℕ →ᵇ A) ⧸ nullSubmodule q ω) :=
  (quotientMap q ω R hR).mkContinuous ‖R‖ (norm_quotientMap_le q ω R hR)

end NullSubmodule

section ClosedNullSpace
variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]

theorem isClosed_nullSubmodule (q : A →L[ℂ] E) (ω : Filter ℕ) :
    IsClosed (nullSubmodule q.toLinearMap ω : Set (ℕ →ᵇ A)) := by
  apply isClosed_of_closure_subset
  intro x hx
  change x ∈ nullSubmodule q.toLinearMap ω
  rw [mem_nullSubmodule]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hc : 0 < ‖q‖ + 1 := by positivity
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2 / (‖q‖ + 1))
    (by positivity)
  have hsmall : ‖q‖ * ‖x - y‖ < ε / 2 := by
    have hd : ‖x - y‖ < ε / 2 / (‖q‖ + 1) := by
      simpa only [dist_eq_norm] using hxy
    calc
      _ ≤ (‖q‖ + 1) * ‖x - y‖ := by gcongr; linarith
      _ < (‖q‖ + 1) * (ε / 2 / (‖q‖ + 1)) := mul_lt_mul_of_pos_left hd hc
      _ = _ := by field_simp
  have hy' := ((mem_nullSubmodule q.toLinearMap ω y).mp hy).eventually_lt_const
    (half_pos hε)
  filter_upwards [hy'] with j hj
  have hdiff : ‖q (x j) - q (y j)‖ < ε / 2 := by
    calc
      _ = ‖q ((x - y) j)‖ := by simp
      _ ≤ ‖q‖ * ‖(x - y) j‖ := q.le_opNorm _
      _ ≤ ‖q‖ * ‖x - y‖ := by gcongr; exact (x - y).norm_coe_le_norm j
      _ < _ := hsmall
  have hn := norm_le_norm_sub_add (q (x j)) (q (y j))
  simp only [dist_zero_right, Real.norm_eq_abs, abs_norm]
  change ‖q (x j)‖ < ε
  change ‖q (y j)‖ < ε / 2 at hj
  linarith

end ClosedNullSpace

section UltraSeminorm
variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]
variable (q : A →L[ℂ] E) (ω : Ultrafilter ℕ)

def sequenceTwoNorm (x : ℕ →ᵇ A) : ℝ :=
  (ω : Filter ℕ).limUnder (fun j => ‖q (x j)‖)

theorem tendsto_sequenceTwoNorm (x : ℕ →ᵇ A) :
    Tendsto (fun j => ‖q (x j)‖) (ω : Filter ℕ) (𝓝 (sequenceTwoNorm q ω x)) := by
  have hbound : ∀ j, ‖q (x j)‖ ∈ Set.Icc 0 (‖q‖ * ‖x‖) := by
    intro j
    exact ⟨norm_nonneg _, (q.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (x.norm_coe_le_norm j) (norm_nonneg _))⟩
  obtain ⟨a, _, ha⟩ := (isCompact_Icc : IsCompact (Set.Icc 0 (‖q‖ * ‖x‖))).ultrafilter_le_nhds
    (ω.map (fun j => ‖q (x j)‖)) (by
      rw [Ultrafilter.coe_map, le_principal_iff]
      change ∀ᶠ j in (ω : Filter ℕ), ‖q (x j)‖ ∈ Set.Icc 0 (‖q‖ * ‖x‖)
      exact Eventually.of_forall hbound)
  have ht : Tendsto (fun j => ‖q (x j)‖) (ω : Filter ℕ) (𝓝 a) := ha
  simpa only [sequenceTwoNorm, ht.limUnder_eq] using ht

theorem sequenceTwoNorm_nonneg (x : ℕ →ᵇ A) : 0 ≤ sequenceTwoNorm q ω x :=
  ge_of_tendsto' (tendsto_sequenceTwoNorm q ω x) (fun _ => norm_nonneg _)

theorem sequenceTwoNorm_eq_of_sub_mem (x y : ℕ →ᵇ A)
    (h : x - y ∈ nullSubmodule q.toLinearMap (ω : Filter ℕ)) :
    sequenceTwoNorm q ω x = sequenceTwoNorm q ω y := by
  have hz : Tendsto (fun j => ‖q (x j)‖ - ‖q (y j)‖) (ω : Filter ℕ) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun j => ?_) ((mem_nullSubmodule _ _ _).mp h)
    simpa only [Real.norm_eq_abs, BoundedContinuousFunction.sub_apply, map_sub,
      ContinuousLinearMap.coe_coe] using abs_norm_sub_norm_le (q (x j)) (q (y j))
  have hh := tendsto_nhds_unique
    ((tendsto_sequenceTwoNorm q ω x).sub (tendsto_sequenceTwoNorm q ω y)) hz
  exact sub_eq_zero.mp hh

def quotientTwoNorm : ((ℕ →ᵇ A) ⧸ nullSubmodule q.toLinearMap (ω : Filter ℕ)) → ℝ :=
  Quotient.lift (sequenceTwoNorm q ω) (fun x y h =>
    sequenceTwoNorm_eq_of_sub_mem q ω x y ((Submodule.quotientRel_def _).mp h))

@[simp] theorem quotientTwoNorm_mk (x : ℕ →ᵇ A) :
    quotientTwoNorm q ω (Submodule.Quotient.mk x) = sequenceTwoNorm q ω x := rfl

theorem quotientTwoNorm_nonneg
    (X : (ℕ →ᵇ A) ⧸ nullSubmodule q.toLinearMap (ω : Filter ℕ)) :
    0 ≤ quotientTwoNorm q ω X := by
  induction X using Quotient.inductionOn with | h x => exact sequenceTwoNorm_nonneg q ω x

theorem quotientMap_ballModulus (R : A →L[ℂ] A) (hR : BallModulus q R) :
    BallModulus (quotientTwoNorm q ω)
      (quotientContinuousMap q.toLinearMap (ω : Filter ℕ) R hR) := by
  intro r ε hε
  obtain ⟨δ, hδ, hmod⟩ := hR (r + 1) (ε / 2) (half_pos hε)
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro X hX hXtwo
  obtain ⟨x, rfl, hx⟩ := Submodule.Quotient.norm_mk_lt X zero_lt_one
  have hxtwo : sequenceTwoNorm q ω x < δ := by
    rw [quotientTwoNorm_mk, Real.norm_eq_abs,
      abs_of_nonneg (sequenceTwoNorm_nonneg q ω x)] at hXtwo
    linarith
  have hsmall := (tendsto_sequenceTwoNorm q ω x).eventually_lt_const hxtwo
  have hout : ∀ᶠ j in (ω : Filter ℕ), ‖q (R (x j))‖ ≤ ε / 2 := by
    filter_upwards [hsmall] with j hj
    exact (hmod (x j) ((x.norm_coe_le_norm j).trans (by linarith)) hj).le
  change ‖sequenceTwoNorm q ω (R.compLeftContinuousBounded ℕ x)‖ < ε
  rw [Real.norm_eq_abs, abs_of_nonneg (sequenceTwoNorm_nonneg q ω _)]
  exact lt_of_le_of_lt (le_of_tendsto (tendsto_sequenceTwoNorm q ω
    (R.compLeftContinuousBounded ℕ x)) hout) (by linarith)

theorem quotientTwoNorm_eq_zero_iff
    (X : (ℕ →ᵇ A) ⧸ nullSubmodule q.toLinearMap (ω : Filter ℕ)) :
    quotientTwoNorm q ω X = 0 ↔ X = 0 := by
  induction X using Quotient.inductionOn with
  | h x =>
    constructor
    · intro hx
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [mem_nullSubmodule]
      change sequenceTwoNorm q ω x = 0 at hx
      exact hx ▸ tendsto_sequenceTwoNorm q ω x
    · intro hx
      have hz : x ∈ nullSubmodule q.toLinearMap (ω : Filter ℕ) :=
        (Submodule.Quotient.mk_eq_zero _).mp hx
      exact tendsto_nhds_unique (tendsto_sequenceTwoNorm q ω x)
        ((mem_nullSubmodule _ _ _).mp hz)

end UltraSeminorm

section TraceIdeal
open scoped ComplexOrder
open HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)

variable (ω : Filter ℕ)

theorem nullSubmodule_mul_right (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (x y : ℕ →ᵇ A)
    (hx : x ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap ω) :
    x * y ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap ω := by
  rw [mem_nullSubmodule] at hx ⊢
  change Tendsto (fun j => ‖τ.toPreGNS (x j * y j)‖) ω (𝓝 0)
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun j => (preGNS_norm_mul_right_le τ htr _ _).trans
      (mul_le_mul_of_nonneg_right (y.norm_coe_le_norm j) (norm_nonneg _)))
  simpa only [mul_zero, ContinuousLinearMap.coe_coe, traceHilbertMap_apply] using hx.const_mul ‖y‖

theorem nullSubmodule_star (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (x : ℕ →ᵇ A) (hx : x ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap ω) :
    star x ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap ω := by
  rw [mem_nullSubmodule] at hx ⊢
  simpa only [ContinuousLinearMap.coe_coe, traceHilbertMap_apply,
    BoundedContinuousFunction.star_apply, preGNS_norm_star τ htr] using hx
end TraceIdeal
end
end TracialUltrapower
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
namespace HochschildUltrapower
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open TracialUltrapower HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
include h1

def ideal : Ideal (ℕ →ᵇ A) where
  carrier := nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ)
  zero_mem' := Submodule.zero_mem _
  add_mem' := fun hx hy => Submodule.add_mem _ hx hy
  smul_mem' := fun x y hy => by
    change x*y ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ)
    have hs := nullSubmodule_star τ h1 (ω : Filter ℕ) htr y hy
    have ht := nullSubmodule_mul_right τ h1 (ω : Filter ℕ) htr (star y) (star x) hs
    have hh := nullSubmodule_star τ h1 (ω : Filter ℕ) htr _ ht
    rw [star_mul,star_star,star_star] at hh
    exact hh

instance ideal_twoSided : (ideal τ h1 ω htr).IsTwoSided where
  mul_mem_of_left := fun {x} y hx => nullSubmodule_mul_right τ h1 (ω : Filter ℕ) htr x y hx

instance ideal_starClosed : HochschildCStarQuotient.StarClosed (ideal τ h1 ω htr) where
  star_mem := fun {x} hx => nullSubmodule_star τ h1 (ω : Filter ℕ) htr x hx

instance ideal_closed : IsClosed (ideal τ h1 ω htr : Set (ℕ →ᵇ A)) :=
  isClosed_nullSubmodule (traceHilbertMap τ h1) (ω : Filter ℕ)

abbrev Ultrapower := (ℕ →ᵇ A) ⧸ ideal τ h1 ω htr

instance ultrapowerCStar : CStarAlgebra (Ultrapower τ h1 ω htr) :=
  let _ := ideal_twoSided τ h1 ω htr
  let _ := ideal_starClosed τ h1 ω htr
  HochschildCStarQuotient.quotientCStarAlgebra (ideal τ h1 ω htr)

lemma norm_trace_le (a : A) : ‖τ a‖ ≤ ‖τ.toPreGNS a‖ := by
  have hin : inner ℂ (τ.toPreGNS 1) (τ.toPreGNS a) = τ a := by
    simp [PositiveLinearMap.preGNS_inner_def]
  rw [← hin]
  have hone : ‖τ.toPreGNS 1‖ = 1 := by
    rw [PositiveLinearMap.preGNS_norm_def]
    simp [h1]
  simpa only [hone,one_mul] using norm_inner_le_norm (𝕜 := ℂ) (τ.toPreGNS 1) (τ.toPreGNS a)

def sequenceTrace (x : ℕ →ᵇ A) : ℂ := limUnder (ω : Filter ℕ) (fun j => τ (x j))

lemma tendsto_sequenceTrace (x : ℕ →ᵇ A) :
    Tendsto (fun j => τ (x j)) (ω : Filter ℕ) (nhds (sequenceTrace τ ω x)) := by
  have hb : ∀ j, τ (x j) ∈ Metric.closedBall 0 ‖x‖ := by
    intro j
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (norm_trace_le τ h1 _).trans ((preGNS_norm_le τ h1 _).trans (x.norm_coe_le_norm j))
  obtain ⟨a,_,ha⟩ := (isCompact_closedBall (0:ℂ) ‖x‖).ultrafilter_le_nhds
    (ω.map (fun j => τ (x j))) (by
      rw [Ultrafilter.coe_map,le_principal_iff]
      change ∀ᶠ j in (ω : Filter ℕ), τ (x j) ∈ Metric.closedBall 0 ‖x‖
      exact Eventually.of_forall hb)
  have ht : Tendsto (fun j => τ (x j)) (ω : Filter ℕ) (nhds a) := ha
  simpa only [sequenceTrace,ht.limUnder_eq] using ht

def sequenceTraceLinear : (ℕ →ᵇ A) →ₗ[ℂ] ℂ where
  toFun := sequenceTrace τ ω
  map_add' x y := by
    apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω (x+y))
    simpa only [BoundedContinuousFunction.add_apply,map_add] using
      (tendsto_sequenceTrace τ h1 ω x).add (tendsto_sequenceTrace τ h1 ω y)
  map_smul' c x := by
    apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω (c • x))
    simpa only [BoundedContinuousFunction.smul_apply,map_smul,RingHom.id_apply] using
      (tendsto_sequenceTrace τ h1 ω x).const_smul c

lemma sequenceTrace_null (x : ℕ →ᵇ A) (hx : x ∈ ideal τ h1 ω htr) : sequenceTrace τ ω x = 0 := by
  apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω x)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun j => norm_trace_le τ h1 (x j))
  exact (mem_nullSubmodule _ _ x).mp hx

def quotientTraceLinear : Ultrapower τ h1 ω htr →ₗ[ℂ] ℂ :=
  (nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ)).liftQ
    (sequenceTraceLinear τ h1 ω) (fun x hx => sequenceTrace_null τ h1 ω htr x hx)

@[simp] lemma quotientTraceLinear_mk (x : ℕ →ᵇ A) :
    quotientTraceLinear τ h1 ω htr (Ideal.Quotient.mk (ideal τ h1 ω htr) x) =
      sequenceTrace τ ω x := rfl

instance ultrapowerOrder : PartialOrder (Ultrapower τ h1 ω htr) :=
  CStarAlgebra.spectralOrder _

instance ultrapowerStarOrder : StarOrderedRing (Ultrapower τ h1 ω htr) :=
  CStarAlgebra.spectralOrderedRing _

lemma quotientTraceLinear_nonneg (X : Ultrapower τ h1 ω htr) (hX : 0 ≤ X) :
    0 ≤ quotientTraceLinear τ h1 ω htr X := by
  obtain ⟨Y,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective Y
  change 0 ≤ sequenceTrace τ ω (star y * y)
  apply ge_of_tendsto' (tendsto_sequenceTrace τ h1 ω _)
  intro j
  exact τ.map_nonneg (star_mul_self_nonneg (y j))

def quotientTrace : Ultrapower τ h1 ω htr →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (quotientTraceLinear τ h1 ω htr)
    (quotientTraceLinear_nonneg τ h1 ω htr)

@[simp] lemma quotientTrace_mk (x : ℕ →ᵇ A) :
    quotientTrace τ h1 ω htr (Ideal.Quotient.mk (ideal τ h1 ω htr) x) =
      sequenceTrace τ ω x := rfl

lemma quotientTrace_one : quotientTrace τ h1 ω htr 1 = 1 := by
  change sequenceTrace τ ω (1 : ℕ →ᵇ A) = 1
  apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω _)
  change Tendsto (fun _ : ℕ => τ (1:A)) (ω : Filter ℕ) (nhds 1)
  rw [h1]
  exact tendsto_const_nhds

lemma quotientTrace_tracial (X Y : Ultrapower τ h1 ω htr) :
    quotientTrace τ h1 ω htr (X*Y) = quotientTrace τ h1 ω htr (Y*X) := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective X
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective Y
  change sequenceTrace τ ω (x*y) = sequenceTrace τ ω (y*x)
  apply congrArg (limUnder (ω : Filter ℕ))
  funext j
  exact htr (x j) (y j)

lemma sequenceTrace_star_mul (x : ℕ →ᵇ A) :
    sequenceTrace τ ω (star x * x) =
      (sequenceTwoNorm (traceHilbertMap τ h1) ω x : ℂ)^2 := by
  apply tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω _)
  have hh := ((Complex.continuous_ofReal.tendsto _).comp
    (tendsto_sequenceTwoNorm (traceHilbertMap τ h1) ω x)).pow 2
  convert hh using 1
  ext j
  exact (PositiveLinearMap.preGNS_norm_sq τ (τ.toPreGNS (x j))).symm

lemma quotientTrace_preGNS_norm (X : Ultrapower τ h1 ω htr) :
    ‖(quotientTrace τ h1 ω htr).toPreGNS X‖ =
      quotientTwoNorm (traceHilbertMap τ h1) ω X := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective X
  change ‖(quotientTrace τ h1 ω htr).toPreGNS
    (Ideal.Quotient.mk (ideal τ h1 ω htr) x)‖ =
    sequenceTwoNorm (traceHilbertMap τ h1) ω x
  have hh := congrArg Complex.re
    (PositiveLinearMap.preGNS_norm_sq (quotientTrace τ h1 ω htr)
      ((quotientTrace τ h1 ω htr).toPreGNS (Ideal.Quotient.mk (ideal τ h1 ω htr) x)))
  change ((‖(quotientTrace τ h1 ω htr).toPreGNS
    (Ideal.Quotient.mk (ideal τ h1 ω htr) x)‖ : ℂ)^2).re =
      (sequenceTrace τ ω (star x*x)).re at hh
  rw [sequenceTrace_star_mul τ h1 ω] at hh
  simp only [← Complex.ofReal_pow,Complex.ofReal_re] at hh
  have hn := sequenceTwoNorm_nonneg (traceHilbertMap τ h1) ω x
  nlinarith [norm_nonneg ((quotientTrace τ h1 ω htr).toPreGNS
    (Ideal.Quotient.mk (ideal τ h1 ω htr) x))]

lemma quotientTrace_faithful (X : Ultrapower τ h1 ω htr)
    (hX : quotientTrace τ h1 ω htr (star X * X) = 0) : X = 0 := by
  apply (quotientTwoNorm_eq_zero_iff (traceHilbertMap τ h1) ω X).mp
  rw [← quotientTrace_preGNS_norm τ h1 ω htr]
  rw [PositiveLinearMap.preGNS_norm_def]
  simp [hX]

end HochschildUltrapower

namespace HochschildUltrapower
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open TracialUltrapower HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))

def quotientHom : (ℕ →ᵇ A) →⋆ₐ[ℂ] Ultrapower τ h1 ω htr where
  toRingHom := Ideal.Quotient.mk (ideal τ h1 ω htr)
  commutes' _ := rfl
  map_star' _ := rfl

variable {G : Type*} [Group G]

def boundedHom (u : ℕ → G →* unitary A) : G →* (ℕ →ᵇ A) where
  toFun g := BoundedContinuousFunction.mkOfBound
    ⟨fun j => (u j g : A), continuous_of_discreteTopology⟩ (2*‖(1:A)‖)
    (fun i j => by
      calc
        dist (u i g : A) (u j g : A) = ‖(u i g : A)-(u j g : A)‖ := dist_eq_norm _ _
        _ ≤ ‖(u i g : A)‖ + ‖(u j g : A)‖ := norm_sub_le _ _
        _ = 2*‖(1:A)‖ := by
          have hi := CStarRing.norm_coe_unitary_mul (u i g) (1:A)
          have hj := CStarRing.norm_coe_unitary_mul (u j g) (1:A)
          simp only [mul_one] at hi hj
          rw [hi,hj,two_mul])
  map_one' := by ext j; simp
  map_mul' g h := by ext j; simp

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma boundedHom_apply (u : ℕ → G →* unitary A) (g : G) (j : ℕ) :
    boundedHom u g j = (u j g : A) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma boundedHom_star (u : ℕ → G →* unitary A) (g : G) :
    star (boundedHom u g) = boundedHom u g⁻¹ := by
  ext j
  change star (u j g : A) = (u j g⁻¹ : A)
  rw [map_inv]
  rfl

def quotientFamily (u : ℕ → G →* unitary A) : G →* Ultrapower τ h1 ω htr :=
  (quotientHom τ h1 ω htr).toMonoidHom.comp (boundedHom u)

lemma quotientFamily_star (u : ℕ → G →* unitary A) (g : G) :
    star (quotientFamily τ h1 ω htr u g) = quotientFamily τ h1 ω htr u g⁻¹ := by
  change star (quotientHom τ h1 ω htr (boundedHom u g)) = _
  rw [← map_star,boundedHom_star]
  rfl

lemma quotientFamily_trace_zero (u : ℕ → G →* unitary A) (g : G)
    (hω : (ω : Filter ℕ) ≤ atTop)
    (hg : Tendsto (fun j => τ (u j g : A)) atTop (nhds 0)) :
    quotientTrace τ h1 ω htr (quotientFamily τ h1 ω htr u g) = 0 := by
  exact tendsto_nhds_unique (tendsto_sequenceTrace τ h1 ω (boundedHom u g)) (hg.mono_left hω)

def map (R : A →L[ℂ] A) (hR : BallModulus (traceHilbertMap τ h1) R) :
    Ultrapower τ h1 ω htr →L[ℂ] Ultrapower τ h1 ω htr :=
  quotientContinuousMap (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ) R hR

lemma map_modulus (R : A →L[ℂ] A) (hR : BallModulus (traceHilbertMap τ h1) R) :
    BallModulus (quotientTrace τ h1 ω htr).toPreGNS (map τ h1 ω htr R hR) := by
  have hm := quotientMap_ballModulus (traceHilbertMap τ h1) ω R hR
  intro r ε hε
  obtain ⟨δ,hδ,hmod⟩ := hm r ε hε
  refine ⟨δ,hδ,fun X hX hq => ?_⟩
  rw [quotientTrace_preGNS_norm] at hq ⊢
  have hn := quotientTwoNorm_nonneg (traceHilbertMap τ h1) ω X
  have hn' := quotientTwoNorm_nonneg (traceHilbertMap τ h1) ω (map τ h1 ω htr R hR X)
  have hout := hmod X hX (by simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using hq)
  change |quotientTwoNorm (traceHilbertMap τ h1) ω (map τ h1 ω htr R hR X)| < ε at hout
  rwa [abs_of_nonneg hn'] at hout
end HochschildUltrapower
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
namespace HochschildFirstLetter
open Filter Topology
open scoped ComplexOrder
open HochschildRigidity TracialUltrapower HochschildUltrapower
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end HochschildFirstLetter

namespace HochschildUltrapower
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open TracialUltrapower HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (ω : Ultrafilter ℕ)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
variable {G : Type*} [Group G]

lemma map_asymptotic_identity_sequence (u : ℕ → G →* unitary A) (g : G)
    (hω : (ω : Filter ℕ) ≤ atTop)
    (R : A →L[ℂ] A) (hR : BallModulus (traceHilbertMap τ h1) R) (a : ℕ →ᵇ A)
    (ha : Tendsto (fun j => ‖τ.toPreGNS (R (u j g : A) - a j*(u j g : A))‖) atTop (nhds 0)) :
    map τ h1 ω htr R hR (quotientFamily τ h1 ω htr u g) =
      quotientHom τ h1 ω htr a * quotientFamily τ h1 ω htr u g := by
  apply sub_eq_zero.mp
  change (Ideal.Quotient.mk (ideal τ h1 ω htr))
    (R.compLeftContinuousBounded ℕ (boundedHom u g) - a * boundedHom u g) = 0
  apply (Ideal.Quotient.eq_zero_iff_mem).mpr
  change _ ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ)
  rw [mem_nullSubmodule]
  exact ha.mono_left hω

end HochschildUltrapower

namespace HochschildFirstLetter
open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open HochschildRigidity TracialUltrapower HochschildUltrapower
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem asymptotic_first_letter_endpoints
    (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (R : A →L[ℂ] A) (hR : BallSequential τ.toPreGNS R)
    (u : ℕ → FreeGroup ℕ →* unitary A)
    (hfree : ∀ g : FreeGroup ℕ, g ≠ 1 →
      Tendsto (fun j => τ (u j g : A)) atTop (nhds 0))
    (a b : ℕ →ᵇ A)
    (hw : ∀ (g : FreeGroup ℕ) i t l, g.toWord = (i,t)::l →
      (g.toWord.map Prod.fst).Nodup →
      Tendsto (fun j => ‖τ.toPreGNS (R (u j g : A) - (if t then a j else b j)*(u j g : A))‖)
        atTop (nhds 0)) :
    Tendsto (fun j => ‖τ.toPreGNS (a j - b j)‖) atTop (nhds 0) := by
  rw [Filter.tendsto_iff_ultrafilter]
  intro ω hω
  have hm : BallModulus (traceHilbertMap τ h1) R :=
    (ballSequential_iff_modulus _ _).mp hR
  have he : quotientHom τ h1 ω htr a = quotientHom τ h1 ω htr b := by
    apply countable_first_letter_rigidity (quotientTrace τ h1 ω htr)
      (quotientFamily τ h1 ω htr u) (quotientTrace_one τ h1 ω htr)
      (quotientFamily_star τ h1 ω htr u)
      (fun g hg => quotientFamily_trace_zero τ h1 ω htr u g hω (hfree g hg))
      (quotientTrace_tracial τ h1 ω htr) (quotientTrace_faithful τ h1 ω htr)
      (HochschildUltrapower.map τ h1 ω htr R hm)
    · exact (ballSequential_iff_modulus _ _).mpr (map_modulus τ h1 ω htr R hm)
    · intro g i t l hword hnodup
      cases t with
      | false =>
        exact map_asymptotic_identity_sequence τ h1 ω htr u g hω R hm b
          (hw g i false l hword hnodup)
      | true =>
        exact map_asymptotic_identity_sequence τ h1 ω htr u g hω R hm a
          (hw g i true l hword hnodup)
  have hz : Ideal.Quotient.mk (ideal τ h1 ω htr) (a-b) = 0 := by
    change quotientHom τ h1 ω htr (a-b) = 0
    rw [map_sub,he,sub_self]
  have ha := Ideal.Quotient.eq_zero_iff_mem.mp hz
  change (a-b) ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap (ω : Filter ℕ) at ha
  rw [mem_nullSubmodule] at ha
  exact ha
end HochschildFirstLetter
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace HochschildMartingale

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in

lemma energy_identity (Z : ℕ → H)
    (horth : ∀ k n, k ≤ n → inner ℝ (Z n - Z k) (Z k) = 0) {k n : ℕ} (hkn : k ≤ n) :
    ‖Z n - Z k‖ ^ 2 = ‖Z n‖ ^ 2 - ‖Z k‖ ^ 2 := by
  have h := horth k n hkn
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at h
  rw [norm_sub_sq_real]
  linarith

theorem exists_limit_of_bounded_orthogonal_increments (Z : ℕ → H)
    (horth : ∀ k n, k ≤ n → inner ℝ (Z n - Z k) (Z k) = 0)
    (C : ℝ) (hb : ∀ n, ‖Z n‖ ≤ C) :
    ∃ z : H, Tendsto Z atTop (𝓝 z) ∧
      ∀ k n, k ≤ n → ‖Z n - Z k‖ ^ 2 = ‖z - Z k‖ ^ 2 - ‖z - Z n‖ ^ 2 := by
  have hmono : Monotone (fun n => ‖Z n‖ ^ 2) := by
    intro k n hkn
    have := sq_nonneg ‖Z n-Z k‖
    rw [energy_identity Z horth hkn] at this
    linarith
  have hbd : BddAbove (Set.range (fun n => ‖Z n‖^2)) := by
    refine ⟨C^2, ?_⟩
    rintro x ⟨n,rfl⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (hb n) _
  let L : ℝ := ⨆ n, ‖Z n‖^2
  have hlim : Tendsto (fun n => ‖Z n‖^2) atTop (𝓝 L) := tendsto_atTop_ciSup hmono hbd
  have hc : CauchySeq Z := by
    apply cauchySeq_of_le_tendsto_0' (fun n => Real.sqrt (L-‖Z n‖^2))
    · intro n m hnm
      rw [dist_eq_norm, norm_sub_rev]
      apply Real.le_sqrt_of_sq_le
      rw [energy_identity Z horth hnm]
      exact sub_le_sub_right (le_ciSup hbd m) _
    · simpa only [sub_self, Real.sqrt_zero] using ((tendsto_const_nhds (x := L)).sub hlim).sqrt
  obtain ⟨z,hz⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨z,hz,?_⟩
  intro k n hkn
  have he (i : ℕ) : ‖z-Z i‖^2 = ‖z‖^2-‖Z i‖^2 := by
    have ha : Tendsto (fun m => ‖Z m-Z i‖^2) atTop (𝓝 (‖z-Z i‖^2)) :=
      (hz.sub_const _).norm.pow 2
    have hb' : Tendsto (fun m => ‖Z m‖^2-‖Z i‖^2) atTop (𝓝 (‖z‖^2-‖Z i‖^2)) :=
      (hz.norm.pow 2).sub_const _
    exact tendsto_nhds_unique ha (hb'.congr' (eventually_atTop.2
      ⟨i,fun m hm => (energy_identity Z horth hm).symm⟩))
  rw [he k,he n,energy_identity Z horth hkn]
  ring

theorem uniform_cauchy_error (Z : ℕ → H)
    (horth : ∀ k n, k ≤ n → inner ℝ (Z n - Z k) (Z k) = 0)
    (C : ℝ) (hb : ∀ n, ‖Z n‖ ≤ C) :
    ∃ z : H, Tendsto Z atTop (𝓝 z) ∧
      Tendsto (fun k => ‖z-Z k‖^2) atTop (𝓝 0) ∧
      ∀ k n, k ≤ n → ‖Z n-Z k‖^2 ≤ ‖z-Z k‖^2 := by
  obtain ⟨z,hz,he⟩ := exists_limit_of_bounded_orthogonal_increments Z horth C hb
  refine ⟨z,hz,?_,fun k n hkn => ?_⟩
  · simpa using ((tendsto_const_nhds (x := z)).sub hz).norm.pow 2
  · rw [he k n hkn]
    exact sub_le_self _ (sq_nonneg _)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {f : ℕ → Ω → H}

end HochschildMartingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def pathMeasure : Measure (ℕ → G) := Measure.infinitePi (fun _ : ℕ => μ)
instance : IsProbabilityMeasure (pathMeasure μ) := by unfold pathMeasure; infer_instance

def takePath (n : ℕ) (ω : ℕ → G) : Fin n → G := fun i => ω i

def walk (n : ℕ) (ω : ℕ → G) : G := word (takePath n ω)

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma walk_succ (n : ℕ) (ω : ℕ → G) : walk (n+1) ω = walk n ω * ω n := by
  unfold walk word
  rw [List.ofFn_succ', List.prod_concat]
  rfl

omit [Group G] [Countable G] [MeasurableSingletonClass G] in
lemma takePath_measurable (n : ℕ) : Measurable (takePath (G := G) n) := by
  exact measurable_pi_iff.mpr (fun index : Fin n => measurable_pi_apply (index : ℕ))

omit [Group G] [Countable G] [MeasurableSingletonClass G] in
lemma takePath_law (n : ℕ) : (pathMeasure μ).map (takePath n) = Measure.pi (fun _ : Fin n => μ) := by
  have h := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => μ)
    (f := (Fin.val : Fin n → ℕ)) Fin.val_injective
  change (Measure.infinitePi (fun _ : ℕ => μ)).map (fun ω (i : Fin n) => ω (i : ℕ)) = _
  rw [h, Measure.infinitePi_eq_pi]

lemma walk_measurable (n : ℕ) : Measurable (walk (G := G) n) :=
  (measurable_of_countable (word (G := G) (n := n))).comp (takePath_measurable n)

omit [CompleteSpace H] [Group G] in
lemma takePath_integral (n : ℕ) (F : (Fin n → G) → H) :
    ∫ ω, F (takePath n ω) ∂pathMeasure μ = ∫ w, F w ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [← takePath_law μ n]
  exact (integral_map (takePath_measurable n).aemeasurable
    (StronglyMeasurable.of_discrete (f := F)).aestronglyMeasurable).symm

omit [Group G] [MeasurableSingletonClass G] [CompleteSpace H] in

lemma last_integral (n : ℕ) (F : (Fin n → G) → G → H)
    (hF : Integrable (fun p : (Fin n → G) × G => F p.1 p.2)
      ((Measure.pi (fun _ : Fin n => μ)).prod μ)) :
    ∫ v : Fin (n+1) → G, F (fun i => v i.castSucc) (v (Fin.last n))
      ∂Measure.pi (fun _ : Fin (n+1) => μ) =
    ∫ w : Fin n → G, ∫ u, F w u ∂μ ∂Measure.pi (fun _ : Fin n => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) (Fin.last n)).integral_comp'
    (fun p => F p.2 p.1)
  have he : ∀ v : Fin (n+1) → G,
      (fun p : G × (Fin n → G) => F p.2 p.1)
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => G) (Fin.last n)) v) =
      F (fun i => v i.castSucc) (v (Fin.last n)) := by
    intro v
    simp [MeasurableEquiv.piFinSuccAbove]
    rfl
  simp only [he] at h
  rw [h]
  calc
    _ = ∫ p : (Fin n → G) × G, F p.1 p.2 ∂(Measure.pi (fun _ : Fin n => μ)).prod μ :=
      integral_prod_swap (fun p : (Fin n → G) × G => F p.1 p.2)
    _ = _ := integral_prod _ hF

omit [InnerProductSpace ℝ H] [CompleteSpace H] in

lemma integrable_of_countable_bound {S : Type*} [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsFiniteMeasure ν]
    (f : S → H) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) : Integrable f ν :=
  Integrable.of_bound (StronglyMeasurable.of_discrete (f := f)).aestronglyMeasurable C
    (Filter.Eventually.of_forall hb)

lemma increment_inner_integral (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C)
    (hh : ∀ g, ∫ u, D (g*u) ∂μ = D g) (n : ℕ)
    (Y : (Fin n → G) → H) (B : ℝ) (hY : ∀ w, ‖Y w‖ ≤ B) :
    ∫ ω, inner ℝ (D (walk (n+1) ω)-D (walk n ω)) (Y (takePath n ω)) ∂pathMeasure μ = 0 := by
  let F (w : Fin n → G) (u : G) := inner ℝ (D (word w*u)-D (word w)) (Y w)
  have hF : ∀ w u, ‖F w u‖ ≤ (C+C)*B := by
    intro w u
    calc
      _ ≤ ‖D (word w*u)-D (word w)‖ * ‖Y w‖ := norm_inner_le_norm _ _
      _ ≤ (C+C)*B := mul_le_mul
        ((norm_sub_le _ _).trans (add_le_add (hD _) (hD _))) (hY _) (norm_nonneg _)
        (add_nonneg ((norm_nonneg (D 1)).trans (hD 1)) ((norm_nonneg (D 1)).trans (hD 1)))
  have hstep : ∀ w, ∫ u, F w u ∂μ = 0 := by
    intro w
    have hi : Integrable (fun u => D (word w*u)) μ := integrable_of_countable_bound μ _ C (fun _ => hD _)
    simp_rw [show F w = fun u => inner ℝ (D (word w*u)-D (word w)) (Y w) from rfl,
      real_inner_comm]
    have he := integral_inner (𝕜 := ℝ) (hi.sub (integrable_const (D (word w)))) (Y w)
    simp only [Pi.sub_apply] at he
    rw [he, integral_sub hi (integrable_const _), hh, integral_const]
    simp
  have hhF := integrable_of_countable_bound
    ((Measure.pi (fun _ : Fin n => μ)).prod μ) (fun p => F p.1 p.2) ((C+C)*B)
    (fun p => hF p.1 p.2)
  have hm : (fun ω => inner ℝ (D (walk (n+1) ω)-D (walk n ω)) (Y (takePath n ω))) =
      fun ω => (fun v : Fin (n+1) → G => F (fun i => v i.castSucc) (v (Fin.last n)))
        (takePath (n+1) ω) := by
    funext ω
    rw [walk_succ]
    rfl
  rw [hm, takePath_integral μ (n+1) (fun v => F (fun i => v i.castSucc) (v (Fin.last n))),
    last_integral μ n F hhF]
  simp [hstep]

omit [CompleteSpace H] [InnerProductSpace ℝ H] in
lemma process_memLp (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (n : ℕ) :
    MemLp (fun ω => D (walk n ω)) 2 (pathMeasure μ) :=
  MemLp.of_bound ((StronglyMeasurable.of_discrete (f := D)).comp_measurable
    (walk_measurable n)).aestronglyMeasurable C (Filter.Eventually.of_forall (fun _ => hD _))

def processLp (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (n : ℕ) :
    Lp H 2 (pathMeasure μ) := (process_memLp μ D C hD n).toLp (fun ω => D (walk n ω))

omit [CompleteSpace H] [InnerProductSpace ℝ H] in
lemma processLp_ae (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (n : ℕ) :
    processLp μ D C hD n =ᵐ[pathMeasure μ] fun ω => D (walk n ω) :=
  (process_memLp μ D C hD n).coeFn_toLp

omit [CompleteSpace H] [InnerProductSpace ℝ H] in
lemma processLp_norm_le (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (n : ℕ) :
    ‖processLp μ D C hD n‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg (D 1)).trans (hD 1)
  have ha : ∀ᵐ ω ∂pathMeasure μ, ‖processLp μ D C hD n ω‖ ≤ C := by
    filter_upwards [processLp_ae μ D C hD n] with ω hω
    rw [hω]
    exact hD _
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hC ha

lemma processLp_step_orthogonal (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C)
    (hh : ∀ g, ∫ u, D (g*u) ∂μ = D g) {k n : ℕ} (hkn : k ≤ n) :
    inner ℝ (processLp μ D C hD (n+1)-processLp μ D C hD n) (processLp μ D C hD k) = 0 := by
  let Y (w : Fin n → G) : H := D (word (fun i : Fin k => w (Fin.castLE hkn i)))
  have he := increment_inner_integral μ D C hD hh n Y C (fun _ => hD _)
  rw [L2.inner_def]
  calc
    _ = ∫ ω, inner ℝ (D (walk (n+1) ω)-D (walk n ω)) (Y (takePath n ω)) ∂pathMeasure μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (processLp μ D C hD (n+1)) (processLp μ D C hD n),
        processLp_ae μ D C hD (n+1), processLp_ae μ D C hD n,
        processLp_ae μ D C hD k] with ω hs hn hn' hk
      rw [hs,Pi.sub_apply,hn,hn',hk]
      rfl
    _ = 0 := he

lemma processLp_orthogonal (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C)
    (hh : ∀ g, ∫ u, D (g*u) ∂μ = D g) {k n : ℕ} (hkn : k ≤ n) :
    inner ℝ (processLp μ D C hD n-processLp μ D C hD k) (processLp μ D C hD k) = 0 := by
  induction n, hkn using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    have hs := processLp_step_orthogonal μ D C hD hh hkn
    have he : processLp μ D C hD (n+1)-processLp μ D C hD k =
        (processLp μ D C hD (n+1)-processLp μ D C hD n) +
        (processLp μ D C hD n-processLp μ D C hD k) := by abel
    rw [he,inner_add_left,hs,ih,add_zero]

end HochschildWalk

namespace HochschildWalk
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma processLp_sq_error (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (k n : ℕ) :
    ‖processLp μ D C hD n-processLp μ D C hD k‖ ^ 2 =
      ∫ ω, ‖D (walk n ω)-D (walk k ω)‖ ^ 2 ∂pathMeasure μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (processLp μ D C hD n) (processLp μ D C hD k),
    processLp_ae μ D C hD n, processLp_ae μ D C hD k] with ω hs hn hk
  rw [hs, Pi.sub_apply, hn, hk, real_inner_self_eq_norm_sq]

omit [CompleteSpace H] in
lemma limitLp_sq_error (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C)
    (z : Lp H 2 (pathMeasure μ)) (n : ℕ) :
    ‖z-processLp μ D C hD n‖ ^ 2 =
      ∫ ω, ‖z ω-D (walk n ω)‖ ^ 2 ∂pathMeasure μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub z (processLp μ D C hD n),
    processLp_ae μ D C hD n] with ω hs hn
  rw [hs, Pi.sub_apply, hn, real_inner_self_eq_norm_sq]

theorem harmonic_mean_square_convergence (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C)
    (hh : ∀ g, ∫ u, D (g*u) ∂μ = D g) :
    ∃ z : Lp H 2 (pathMeasure μ),
      Tendsto (fun n => processLp μ D C hD n) atTop (𝓝 z) ∧
      Tendsto (fun n => ∫ ω, ‖z ω-D (walk n ω)‖^2 ∂pathMeasure μ) atTop (𝓝 0) ∧
      ∀ k n, k ≤ n →
        ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
          ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ := by
  obtain ⟨z,hz,he,hb⟩ := HochschildMartingale.uniform_cauchy_error (processLp μ D C hD)
    (fun _ _ hkn => processLp_orthogonal μ D C hD hh hkn) C (processLp_norm_le μ D C hD)
  refine ⟨z,hz,?_,?_⟩
  · simpa only [limitLp_sq_error] using he
  · intro k n hkn
    rw [← processLp_sq_error μ D C hD k n, ← limitLp_sq_error μ D C hD z k]
    exact hb k n hkn
end HochschildWalk
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]

omit [Group G] [Countable G] [MeasurableSingletonClass G] in

lemma iid_extract {I J : Type*} [Fintype J] (index : J → I) (hi : Function.Injective index)
    (f : J → G → G) (hf : ∀ j, MeasurePreserving (f j) μ μ) :
    MeasurePreserving (fun x j => f j (x (index j)))
      (Measure.infinitePi (fun _ : I => μ)) (Measure.pi (fun _ : J => μ)) := by
  have he : MeasurePreserving (fun x j => x (index j))
      (Measure.infinitePi (fun _ : I => μ)) (Measure.pi (fun _ : J => μ)) := by
    refine ⟨measurable_pi_iff.mpr (fun coordinate => measurable_pi_apply (index coordinate)), ?_⟩
    rw [Measure.map_infinitePi_infinitePi_of_inj hi, Measure.infinitePi_eq_pi]
  exact (measurePreserving_pi _ _ hf).comp he

def signed (s : Bool) (g : G) : G := if s then g else g⁻¹

omit [IsProbabilityMeasure μ] in
lemma signed_preserving (hsym : μ.map (fun g => g⁻¹) = μ) (s : Bool) :
    MeasurePreserving (signed s) μ μ := by
  cases s
  · exact ⟨measurable_of_countable _, hsym⟩
  · exact MeasurePreserving.id μ

lemma iid_signed_extract {I J : Type*} [Fintype J] (hsym : μ.map (fun g => g⁻¹) = μ)
    (index : J → I) (hi : Function.Injective index) (sign : J → Bool) :
    MeasurePreserving (fun x j => signed (sign j) (x (index j)))
      (Measure.infinitePi (fun _ : I => μ)) (Measure.pi (fun _ : J => μ)) :=
  iid_extract μ index hi _ (fun j => signed_preserving μ hsym (sign j))

def reversePath (n : ℕ) (w : Fin n → G) : Fin n → G := fun i => (w i.rev)⁻¹

lemma reversePath_preserving (hsym : μ.map (fun g => g⁻¹) = μ) (n : ℕ) :
    MeasurePreserving (reversePath (G := G) n)
      (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin n => μ)) := by
  have hi : Function.Injective (Fin.rev : Fin n → Fin n) := Fin.rev_injective
  have he := iid_signed_extract μ hsym Fin.rev hi (fun _ => false)
  simp only [Measure.infinitePi_eq_pi] at he
  exact he

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma ofFn_reverse_inv (n : ℕ) (w : Fin n → G) :
    List.ofFn (reversePath n w) = ((List.ofFn w).map (fun g => g⁻¹)).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_map, List.length_ofFn,
      List.getElem_map, reversePath, Fin.rev]
    congr 2
    apply Fin.ext
    dsimp
    omega

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma reversePath_prod (n : ℕ) (w : Fin n → G) :
    (List.ofFn (reversePath n w)).prod = (List.ofFn w).prod⁻¹ := by
  rw [ofFn_reverse_inv, ← List.prod_inv_reverse]

def endpointIndex (n h : ℕ) (hle : 2*h ≤ n) : Fin h ⊕ Fin h → Fin n
  | Sum.inl i => ⟨i, by omega⟩
  | Sum.inr i => ⟨n-1-i, by omega⟩

omit [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma endpointIndex_injective (n h : ℕ) (hle : 2*h ≤ n) :
    Function.Injective (endpointIndex n h hle) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      apply congrArg Sum.inl
      apply Fin.ext
      exact congrArg (fun k : Fin n => k.val) hab
    | inr b =>
      have he := congrArg Fin.val hab
      simp only [endpointIndex] at he
      omega
  | inr a =>
    cases b with
    | inl b =>
      have he := congrArg Fin.val hab
      simp only [endpointIndex] at he
      omega
    | inr b =>
      apply congrArg Sum.inr
      apply Fin.ext
      have he := congrArg Fin.val hab
      simp only [endpointIndex] at he
      omega

lemma endpoint_prefixes_preserving (hsym : μ.map (fun g => g⁻¹) = μ)
    (n h : ℕ) (hle : 2*h ≤ n) :
    MeasurePreserving (fun w : Fin n → G =>
      ((fun i : Fin h => w ⟨i, by omega⟩), (fun i : Fin h => (w ⟨n-1-i, by omega⟩)⁻¹)))
      (Measure.pi (fun _ : Fin n => μ))
      ((Measure.pi (fun _ : Fin h => μ)).prod (Measure.pi (fun _ : Fin h => μ))) := by
  have he := iid_signed_extract μ hsym (endpointIndex n h hle)
    (endpointIndex_injective n h hle) (Sum.elim (fun _ => true) (fun _ => false))
  have hf := (measurePreserving_sumPiEquivProdPi (fun _ : Fin h ⊕ Fin h => μ)).comp he
  simp only [Measure.infinitePi_eq_pi] at hf
  exact hf

end HochschildWalk

open MeasureTheory Filter Topology
namespace HochschildProbability
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

lemma mass_transfer (S T E : Set Ω) (h : S ⊆ T ∪ E) :
    μ.real S ≤ μ.real T + μ.real E :=
  (measureReal_mono h).trans (measureReal_union_le _ _)

lemma mass_transfer_two (S T E F : Set Ω) (h : S ⊆ T ∪ (E ∪ F)) :
    μ.real S ≤ μ.real T + μ.real E + μ.real F := by
  have h₁ := mass_transfer μ S T (E∪F) h
  have h₂ := measureReal_union_le (μ := μ) E F
  linarith

omit [IsFiniteMeasure μ] in
lemma norm_error_mass {H : Type*} [NormedAddCommGroup H] (f : Ω → H)
    (hf : MemLp f 2 μ) {δ : ℝ} (hδ : 0 < δ) :
    μ.real {x | δ ≤ ‖f x‖} ≤ (∫ x, ‖f x‖^2 ∂μ) / δ^2 := by
  have he : {x | δ ≤ ‖f x‖} = {x | δ^2 ≤ ‖f x‖^2} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    exact (sq_le_sq₀ hδ.le (norm_nonneg _)).symm
  rw [he, le_div_iff₀ (sq_pos_of_pos hδ), mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
    (hf.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)) _

lemma ball_mass_transfer {H : Type*} [NormedAddCommGroup H] (f g : Ω → H)
    (a : H) {r δ : ℝ} (hδ : 0 < δ) (hfg : MemLp (fun x => f x-g x) 2 μ) :
    μ.real {x | ‖f x-a‖ < r} ≤ μ.real {x | ‖g x-a‖ < r+δ} +
      (∫ x, ‖f x-g x‖^2 ∂μ) / δ^2 := by
  apply (mass_transfer μ _ {x | ‖g x-a‖ < r+δ} {x | δ ≤ ‖f x-g x‖} ?_).trans
  · have hb := norm_error_mass μ (fun x => f x-g x) hfg hδ
    exact add_le_add le_rfl hb
  · intro x hx
    by_cases he : δ ≤ ‖f x-g x‖
    · exact Or.inr he
    · apply Or.inl
      have ht : ‖g x-a‖ ≤ ‖g x-f x‖ + ‖f x-a‖ := by
        simpa only [dist_eq_norm] using dist_triangle (g x) (f x) a
      rw [norm_sub_rev (g x) (f x)] at ht
      dsimp at hx ⊢
      exact ht.trans_lt (add_lt_add (lt_of_not_ge he) hx) |>.trans_eq (add_comm δ r)

lemma two_ball_mass_transfer {H : Type*} [NormedAddCommGroup H]
    (f₁ f₂ g₁ g₂ : Ω → H) (a b : H) {r δ : ℝ} (hδ : 0 < δ)
    (h₁ : MemLp (fun x => f₁ x-g₁ x) 2 μ) (h₂ : MemLp (fun x => f₂ x-g₂ x) 2 μ) :
    μ.real {x | ‖f₁ x-a‖ < r ∧ ‖f₂ x-b‖ < r} ≤
      μ.real {x | ‖g₁ x-a‖ < r+δ ∧ ‖g₂ x-b‖ < r+δ} +
      (∫ x, ‖f₁ x-g₁ x‖^2 ∂μ) / δ^2 + (∫ x, ‖f₂ x-g₂ x‖^2 ∂μ) / δ^2 := by
  have hb₁ := norm_error_mass μ (fun x => f₁ x-g₁ x) h₁ hδ
  have hb₂ := norm_error_mass μ (fun x => f₂ x-g₂ x) h₂ hδ
  have ht := mass_transfer_two μ {x | ‖f₁ x-a‖ < r ∧ ‖f₂ x-b‖ < r}
    {x | ‖g₁ x-a‖ < r+δ ∧ ‖g₂ x-b‖ < r+δ}
    {x | δ ≤ ‖f₁ x-g₁ x‖} {x | δ ≤ ‖f₂ x-g₂ x‖} (by
      intro x hx
      by_cases he₁ : δ ≤ ‖f₁ x-g₁ x‖
      · exact Or.inr (Or.inl he₁)
      by_cases he₂ : δ ≤ ‖f₂ x-g₂ x‖
      · exact Or.inr (Or.inr he₂)
      left
      constructor
      · have hr : ‖g₁ x-a‖ ≤ ‖g₁ x-f₁ x‖ + ‖f₁ x-a‖ := by
          simpa only [dist_eq_norm] using dist_triangle (g₁ x) (f₁ x) a
        rw [norm_sub_rev (g₁ x) (f₁ x)] at hr
        exact hr.trans_lt (add_lt_add (lt_of_not_ge he₁) hx.1) |>.trans_eq (add_comm δ r)
      · have hr : ‖g₂ x-b‖ ≤ ‖g₂ x-f₂ x‖ + ‖f₂ x-b‖ := by
          simpa only [dist_eq_norm] using dist_triangle (g₂ x) (f₂ x) b
        rw [norm_sub_rev (g₂ x) (f₂ x)] at hr
        exact hr.trans_lt (add_lt_add (lt_of_not_ge he₂) hx.2) |>.trans_eq (add_comm δ r))
  exact ht.trans (add_le_add (add_le_add le_rfl hb₁) hb₂)

end HochschildProbability

open MeasureTheory ProbabilityTheory Filter Topology
namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (μ : Measure G) [IsProbabilityMeasure μ]

omit [Group G] [CompleteSpace H] [InnerProductSpace ℝ H] in
lemma finite_memLp (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C)
    (n : ℕ) (f : (Fin n → G) → G) :
    MemLp (fun w => D (f w)) 2 (Measure.pi (fun _ : Fin n => μ)) :=
  MemLp.of_bound (StronglyMeasurable.of_discrete.aestronglyMeasurable) C
    (Eventually.of_forall fun _ => hD _)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma finite_ball_mass (D : G → H) (n : ℕ) (a : H) (r : ℝ) :
    (pathMeasure μ).real {ω | ‖D (walk n ω)-a‖ < r} =
      (Measure.pi (fun _ : Fin n => μ)).real {w | ‖D (word w)-a‖ < r} := by
  have hm : MeasurePreserving (takePath (G := G) n) (pathMeasure μ)
      (Measure.pi (fun _ : Fin n => μ)) := ⟨takePath_measurable n, takePath_law μ n⟩
  exact congrArg ENNReal.toReal (hm.measure_preimage (s := {w | ‖D (word w)-a‖ < r}) (Set.to_countable _).measurableSet.nullMeasurableSet)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma finite_cauchy_bound (D : G → H)
    (z : Lp H 2 (pathMeasure μ))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    (k n : ℕ) (hkn : k ≤ n) :
    ∫ w : Fin n → G, ‖D (word w)-D (word (fun i : Fin k => w (Fin.castLE hkn i)))‖^2
      ∂Measure.pi (fun _ : Fin n => μ) ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ := by
  rw [← takePath_integral μ n]
  exact hc k n hkn

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma endpoint_prefix_ball_mass (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (n k : ℕ) (hkn : 2*k ≤ n) (a b : H) (r : ℝ) :
    (Measure.pi (fun _ : Fin n => μ)).real {w |
      ‖D (word (fun i : Fin k => w ⟨i, by omega⟩))-a‖ < r ∧
      ‖D (word (fun i : Fin k => (w ⟨n-1-i, by omega⟩)⁻¹))-b‖ < r} =
    (pathMeasure μ).real {ω | ‖D (walk k ω)-a‖ < r} *
      (pathMeasure μ).real {ω | ‖D (walk k ω)-b‖ < r} := by
  rw [finite_ball_mass μ D k a r, finite_ball_mass μ D k b r]
  rw [← measureReal_prod_prod]
  exact congrArg ENNReal.toReal ((endpoint_prefixes_preserving μ hsym n k hkn).measure_preimage
    (s := {w | ‖D (word w)-a‖ < r} ×ˢ {w | ‖D (word w)-b‖ < r})
    (Set.to_countable _).measurableSet.nullMeasurableSet)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma reverse_finite_cauchy_bound (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (z : Lp H 2 (pathMeasure μ))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    (k n : ℕ) (hkn : k ≤ n) :
    ∫ w : Fin n → G, ‖D ((word w)⁻¹) - D (word (fun i : Fin k => (w ⟨n-1-i, by omega⟩)⁻¹))‖^2
      ∂Measure.pi (fun _ : Fin n => μ) ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ := by
  have he := (integral_map_of_stronglyMeasurable (μ := Measure.pi (fun _ : Fin n => μ)) (reversePath_preserving μ hsym n).measurable
    (StronglyMeasurable.of_discrete (f := fun w : Fin n → G =>
      ‖D (word w)-D (word (fun i : Fin k => w (Fin.castLE hkn i)))‖^2))).symm
  rw [(reversePath_preserving μ hsym n).map_eq] at he
  have hx : (fun w : Fin n → G =>
      ‖D (word (reversePath n w))-D (word (fun i : Fin k => reversePath n w (Fin.castLE hkn i)))‖^2) =
      (fun w => ‖D ((word w)⁻¹)-D (word (fun i : Fin k => (w ⟨n-1-i, by omega⟩)⁻¹))‖^2) := by
    funext w
    rw [show word (reversePath n w) = (word w)⁻¹ from reversePath_prod n w]
    have hp : (fun i : Fin k => reversePath n w (Fin.castLE hkn i)) =
        (fun i : Fin k => (w ⟨n-1-i, by omega⟩)⁻¹) := by
      funext i
      dsimp [reversePath]
      congr 2
      apply Fin.ext
      dsimp [Fin.rev]
      omega
    rw [hp]
  change (∫ w, _ ∂_) = _ at he
  rw [show (fun w : Fin n → G =>
      (fun v => ‖D (word v)-D (word (fun i : Fin k => v (Fin.castLE hkn i)))‖^2) (reversePath n w)) = _ from hx] at he
  rw [he]
  exact finite_cauchy_bound μ D z hc k n hkn

omit [InnerProductSpace ℝ H] [CompleteSpace H] in

lemma two_endpoint_lower_bound (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (z : Lp H 2 (pathMeasure μ))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    (k n : ℕ) (hkn : 2*k ≤ n) (a b : H) (r δ : ℝ) (hδ : 0 < δ) :
    (pathMeasure μ).real {ω | ‖D (walk k ω)-a‖ < r} *
      (pathMeasure μ).real {ω | ‖D (walk k ω)-b‖ < r} -
        2 * (∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ) / δ^2 ≤
      (Measure.pi (fun _ : Fin n => μ)).real
        {w | ‖D (word w)-a‖ < r+δ ∧ ‖D ((word w)⁻¹)-b‖ < r+δ} := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  let A : (Fin n → G) → H := fun w => D (word (fun i : Fin k => w ⟨i, by omega⟩))
  let B : (Fin n → G) → H := fun w => D (word (fun i : Fin k => (w ⟨n-1-i, by omega⟩)⁻¹))
  let X : (Fin n → G) → H := fun w => D (word w)
  let Y : (Fin n → G) → H := fun w => D ((word w)⁻¹)
  let e := ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ
  have hi₁ : (∫ w, ‖A w-X w‖^2 ∂ν) ≤ e := by
    calc
      _ = ∫ w, ‖X w-A w‖^2 ∂ν := integral_congr_ae (Eventually.of_forall fun w => by rw [norm_sub_rev])
      _ ≤ e := finite_cauchy_bound μ D z hc k n (by omega)
  have hi₂ : (∫ w, ‖B w-Y w‖^2 ∂ν) ≤ e := by
    calc
      _ = ∫ w, ‖Y w-B w‖^2 ∂ν := integral_congr_ae (Eventually.of_forall fun w => by rw [norm_sub_rev])
      _ ≤ e := reverse_finite_cauchy_bound μ hsym D z hc k n (by omega)
  have hb := HochschildProbability.two_ball_mass_transfer ν A B X Y a b (r := r) hδ
    ((finite_memLp μ D C hD n _).sub (finite_memLp μ D C hD n _))
    ((finite_memLp μ D C hD n _).sub (finite_memLp μ D C hD n _))
  have hm : ν.real {w | ‖A w-a‖ < r ∧ ‖B w-b‖ < r} =
      (pathMeasure μ).real {ω | ‖D (walk k ω)-a‖ < r} *
        (pathMeasure μ).real {ω | ‖D (walk k ω)-b‖ < r} :=
    endpoint_prefix_ball_mass μ hsym D n k hkn a b r
  rw [hm] at hb
  apply sub_le_iff_le_add.mpr
  calc
    _ ≤ ν.real {w | ‖X w-a‖ < r+δ ∧ ‖Y w-b‖ < r+δ} +
        (∫ w, ‖A w-X w‖^2 ∂ν) / δ^2 + (∫ w, ‖B w-Y w‖^2 ∂ν) / δ^2 := hb
    _ ≤ ν.real {w | ‖X w-a‖ < r+δ ∧ ‖Y w-b‖ < r+δ} + e/δ^2 + e/δ^2 :=
      add_le_add (add_le_add le_rfl (div_le_div_of_nonneg_right hi₁ (sq_nonneg _)))
        (div_le_div_of_nonneg_right hi₂ (sq_nonneg _))
    _ = _ := by change _ = _ + 2*e/δ^2; ring

omit [InnerProductSpace ℝ H] [CompleteSpace H] in

theorem endpoint_mass_eventually (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (z : Lp H 2 (pathMeasure μ))
    (hz : Tendsto (fun k => ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ) atTop (𝓝 0))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    (a b : H) (ha : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-a‖ < r})
    (hb : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-b‖ < r})
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η > 0, ∃ N : ℕ, ∀ n ≥ N,
      η ≤ (Measure.pi (fun _ : Fin n => μ)).real
        {w | ‖D (word w)-a‖ < δ ∧ ‖D ((word w)⁻¹)-b‖ < δ} := by
  let r := δ/3
  have hr : 0 < r := div_pos hδ (by norm_num)
  let pa := (pathMeasure μ).real {ω | ‖z ω-a‖ < r}
  let pb := (pathMeasure μ).real {ω | ‖z ω-b‖ < r}
  have hpa : 0 < pa := ha r hr
  have hpb : 0 < pb := hb r hr
  let q := min (pa/2) (min (pb/2) (pa*pb/16))
  have hq : 0 < q := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have het : Tendsto (fun k => (∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)/r^2)
      atTop (𝓝 0) := by simpa using hz.div_const (r^2)
  obtain ⟨k,hk⟩ := eventually_atTop.mp (het.eventually (gt_mem_nhds hq))
  let e := (∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)/r^2
  have he : e < q := hk k le_rfl
  have heal : e < pa/2 := he.trans_le (min_le_left _ _)
  have hebl : e < pb/2 := he.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heab : e < pa*pb/16 := he.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have ham := HochschildProbability.ball_mass_transfer (pathMeasure μ) z
    (fun ω => D (walk k ω)) a (r := r) hr ((Lp.memLp z).sub (process_memLp μ D C hD k))
  have hbm := HochschildProbability.ball_mass_transfer (pathMeasure μ) z
    (fun ω => D (walk k ω)) b (r := r) hr ((Lp.memLp z).sub (process_memLp μ D C hD k))
  change pa ≤ (pathMeasure μ).real {ω | ‖D (walk k ω)-a‖ < r+r} + e at ham
  change pb ≤ (pathMeasure μ).real {ω | ‖D (walk k ω)-b‖ < r+r} + e at hbm
  have hA : pa/2 ≤ (pathMeasure μ).real {ω | ‖D (walk k ω)-a‖ < r+r} := by linarith
  have hB : pb/2 ≤ (pathMeasure μ).real {ω | ‖D (walk k ω)-b‖ < r+r} := by linarith
  refine ⟨pa*pb/8, by positivity, 2*k, ?_⟩
  intro n hn
  have hp := mul_le_mul hA hB (by positivity : 0 ≤ pb/2) measureReal_nonneg
  have hl := two_endpoint_lower_bound μ hsym D C hD z hc k n hn a b (r+r) r hr
  have heq : r+r+r = δ := by dsimp [r]; ring
  have heq' : 2*(∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)/r^2 = 2*e := by dsimp [e]; ring
  rw [heq, heq'] at hl
  nlinarith
end HochschildWalk
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open MeasureTheory ProbabilityTheory Filter Topology
namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]

def flattenRows {t n : ℕ} (w : Fin t → Fin n → G) : Fin (t*n) → G :=
  fun q => w (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma word_flattenRows {t n : ℕ} (w : Fin t → Fin n → G) :
    word (flattenRows w) = word (fun i => word (w i)) := by
  unfold word
  rw [List.ofFn_mul, List.prod_flatten, List.map_ofFn]
  congr 1
  congr 1
  funext i
  simp only [Function.comp_apply]
  congr 1
  congr 1
  funext j
  have he : (⟨i*n+j, by nlinarith [i.isLt,j.isLt]⟩ : Fin (t*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    dsimp [finProdFinEquiv]
    ac_rfl
  change flattenRows w ⟨i*n+j, _⟩ = w i j
  rw [he]
  simp [flattenRows]

def orientRow {n : ℕ} (s : Bool) (w : Fin n → G) : Fin n → G :=
  fun i => signed s (w (if s then i else i.rev))

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma word_orientRow {n : ℕ} (s : Bool) (w : Fin n → G) :
    word (orientRow s w) = signed s (word w) := by
  cases s
  · exact reversePath_prod n w
  · rfl

def blockIndex {t m n : ℕ} (index : Fin t → Fin m) (sign : Fin t → Bool) :
    Fin t × Fin n → Fin m × Fin n :=
  fun p => (index p.1, if sign p.1 then p.2 else p.2.rev)

lemma blockIndex_injective {t m n : ℕ} (index : Fin t → Fin m) (hi : Function.Injective index)
    (sign : Fin t → Bool) : Function.Injective (blockIndex (n := n) index sign) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ he
  have hii : i=i' := hi (congrArg Prod.fst he)
  subst i'
  have hj := congrArg Prod.snd he
  dsimp [blockIndex] at hj
  by_cases hs : sign i = true
  · simp only [hs, ↓reduceIte] at hj
    exact Prod.ext rfl hj
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hj
    exact Prod.ext rfl (Fin.rev_injective hj)

lemma concatenated_preserving (hsym : μ.map (fun g => g⁻¹) = μ)
    {t m n : ℕ} (index : Fin t → Fin m) (hi : Function.Injective index) (sign : Fin t → Bool) :
    MeasurePreserving
      (fun w : Fin m × Fin n → G => flattenRows (fun i => orientRow (sign i) (fun j => w (index i,j))))
      (Measure.pi (fun _ : Fin m × Fin n => μ)) (Measure.pi (fun _ : Fin (t*n) => μ)) := by
  have hi' : Function.Injective (fun q : Fin (t*n) => blockIndex index sign (finProdFinEquiv.symm q)) :=
    (blockIndex_injective index hi sign).comp finProdFinEquiv.symm.injective
  have he := iid_signed_extract μ hsym _ hi' (fun q => sign (finProdFinEquiv.symm q).1)
  simp only [Measure.infinitePi_eq_pi] at he
  exact he

omit [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma flattenRows_prefix {t n : ℕ} (w : Fin (t+1) → Fin n → G)
    (hle : n ≤ (t+1)*n) :
    (fun i : Fin n => flattenRows w (Fin.castLE hle i)) = w 0 := by
  funext i
  have he : Fin.castLE hle i = finProdFinEquiv ((0 : Fin (t+1)),i) := by
    apply Fin.ext
    simp [finProdFinEquiv]
  rw [he]
  simp [flattenRows]

variable {H : Type*} [NormedAddCommGroup H]

theorem concatenated_cauchy_bound (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (z : Lp H 2 (pathMeasure μ))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    {t m n : ℕ} (index : Fin (t+1) → Fin m) (hi : Function.Injective index)
    (sign : Fin (t+1) → Bool) :
    ∫ w : Fin m × Fin n → G,
      ‖D (word (fun i => signed (sign i) (word (fun j => w (index i,j))))) -
        D (signed (sign 0) (word (fun j => w (index 0,j))))‖^2
      ∂Measure.pi (fun _ : Fin m × Fin n => μ) ≤
      ∫ ω, ‖z ω-D (walk n ω)‖^2 ∂pathMeasure μ := by
  have hn : n ≤ (t+1)*n := by nlinarith
  let F (w : Fin ((t+1)*n) → G) :=
    ‖D (word w)-D (word (fun i : Fin n => w (Fin.castLE hn i)))‖^2
  have he := (integral_map_of_stronglyMeasurable
    (μ := Measure.pi (fun _ : Fin m × Fin n => μ))
    (concatenated_preserving μ hsym index hi sign).measurable
    (StronglyMeasurable.of_discrete (f := F))).symm
  rw [(concatenated_preserving μ hsym index hi sign).map_eq] at he
  calc
    _ = ∫ w : Fin m × Fin n → G,
        F (flattenRows (fun i => orientRow (sign i) (fun j => w (index i,j))))
        ∂Measure.pi (fun _ : Fin m × Fin n => μ) := by
      apply integral_congr_ae (Eventually.of_forall ?_)
      intro w
      dsimp [F]
      rw [word_flattenRows, flattenRows_prefix _ hn]
      simp only [word_orientRow]
    _ = ∫ w, F w ∂Measure.pi (fun _ : Fin ((t+1)*n) => μ) := he
    _ ≤ _ := finite_cauchy_bound μ D z hc n ((t+1)*n) hn

omit [Group G] in

lemma rows_preserving (m n : ℕ) :
    MeasurePreserving (fun w : Fin m × Fin n → G => fun i j => w (i,j))
      (Measure.pi (fun _ : Fin m × Fin n => μ))
      (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => μ))) := by
  refine ⟨measurable_of_countable _, ?_⟩
  have he := Measure.infinitePi_map_curry (μ := fun _ : Fin m => fun _ : Fin n => μ)
  simp only [Measure.infinitePi_eq_pi] at he
  exact he

omit [Group G] in

lemma rows_event_mass (m n : ℕ) (E : Set (Fin n → G)) :
    (Measure.pi (fun _ : Fin m × Fin n => μ)).real {w | ∀ i, (fun j => w (i,j)) ∈ E} =
      ((Measure.pi (fun _ : Fin n => μ)).real E)^m := by
  have hm := (rows_preserving μ m n).measureReal_preimage
    (s := Set.pi Set.univ (fun _ : Fin m => E)) (Set.to_countable _).measurableSet.nullMeasurableSet
  simp only [MeasureTheory.measureReal_def] at hm
  rw [Measure.pi_pi] at hm
  simpa [Set.pi, ENNReal.toReal_pow, MeasureTheory.measureReal_def] using hm

end HochschildWalk

open MeasureTheory ProbabilityTheory Filter Topology
namespace HochschildProbability

theorem finite_requirements_eventually {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : ∀ n, Measure (X n)) [∀ n, IsFiniteMeasure (μ n)]
    (E : ∀ n, Set (X n)) {c : ℝ} (hc : 0 < c)
    (hE : ∀ᶠ n in atTop, c ≤ (μ n).real (E n))
    {I : Type*} (s : Finset I) (B : ∀ n, I → Set (X n))
    (hB : ∀ i ∈ s, Tendsto (fun n => (μ n).real (B n i)) atTop (nhds 0)) :
    ∀ᶠ n in atTop, ∃ x ∈ E n, ∀ i ∈ s, x ∉ B n i := by
  classical
  have ht : Tendsto (fun n => ∑ i ∈ s, (μ n).real (B n i)) atTop (nhds 0) := by
    simpa using tendsto_finsetSum s hB
  filter_upwards [hE, ht.eventually (gt_mem_nhds hc)] with n hEn hBn
  by_contra h
  push Not at h
  have he : E n ⊆ ⋃ i ∈ s, B n i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := h x hx
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hxi⟩⟩
  have hl := (measureReal_mono (μ := μ n) he (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le s (B n))
  exact (not_lt_of_ge (hEn.trans hl)) hBn

end HochschildProbability

namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
variable {H : Type*} [NormedAddCommGroup H]

def evalList {I : Type*} (u : I → G) (l : List (I × Bool)) : G :=
  (l.map (fun a => signed a.2 (u a.1))).prod

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma evalList_ofFn {I : Type*} {t : ℕ} (u : I → G) (f : Fin t → I × Bool) :
    evalList u (List.ofFn f) = word (fun i => signed (f i).2 (u (f i).1)) := by
  simp [evalList, word, List.map_ofFn, Function.comp_def]

lemma list_cauchy_bound (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (z : Lp H 2 (pathMeasure μ))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    {m n : ℕ} (a : Fin m × Bool) (l : List (Fin m × Bool))
    (hl : ((a::l).map Prod.fst).Nodup) :
    ∫ w : Fin m × Fin n → G,
      ‖D (evalList (fun i => word (fun j => w (i,j))) (a::l)) -
        D (signed a.2 (word (fun j => w (a.1,j))))‖^2
      ∂Measure.pi (fun _ : Fin m × Fin n => μ) ≤
      ∫ ω, ‖z ω-D (walk n ω)‖^2 ∂pathMeasure μ := by
  let f : Fin (l.length+1) → Fin m × Bool := (a::l).get
  have hi : Function.Injective (fun k => (f k).1) := by
    intro i j he
    have he' : ((a::l).map Prod.fst).get ⟨i, by simpa using i.isLt⟩ =
        ((a::l).map Prod.fst).get ⟨j, by simpa using j.isLt⟩ := by
      dsimp [f] at he
      simpa only [List.get_eq_getElem, List.getElem_map] using he
    exact Fin.ext (congrArg (fun q : Fin (((a::l).map Prod.fst).length) => q.val)
      (hl.injective_get he'))
  have hb := concatenated_cauchy_bound μ hsym D z hc (n := n) (fun k => (f k).1) hi (fun k => (f k).2)
  have he : List.ofFn f = a::l := List.ofFn_get (a::l)
  have hev (w : Fin m × Fin n → G) :
      evalList (fun i => word (fun j => w (i,j))) (a::l) =
        word (fun k => signed (f k).2 (word (fun j => w ((f k).1,j)))) := by
    rw [← he, evalList_ofFn]
  simpa only [← hev, f, List.get_cons_zero] using hb

theorem finite_walk_selection (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (z : Lp H 2 (pathMeasure μ))
    (hz : Tendsto (fun k => ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ) atTop (𝓝 0))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    (a b : H) (ha : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-a‖ < r})
    (hb : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-b‖ < r})
    (m : ℕ) {I : Type*} (Q : Finset I) (obs : I → (Fin m → G) → ℝ)
    (V : Finset ((Fin m × Bool) × List (Fin m × Bool)))
    (hV : ∀ v ∈ V, ((v.1::v.2).map Prod.fst).Nodup)
    (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (δ : ℝ) (hδ : 0 < δ)
    (hmom : ∀ q ∈ Q, Tendsto (fun k =>
      (Measure.pi (fun _ : Fin m × Fin (time k) => μ)).real
        {w | δ ≤ obs q (fun i => word (fun j => w (i,j)))}) atTop (nhds 0)) :
    ∃ u : Fin m → G,
      (∀ i, ‖D (u i)-a‖ < δ ∧ ‖D ((u i)⁻¹)-b‖ < δ) ∧
      (∀ q ∈ Q, obs q u < δ) ∧
      ∀ v ∈ V, ‖D (evalList u (v.1::v.2))-D (signed v.1.2 (u v.1.1))‖ < δ := by
  classical
  let ν (k : ℕ) := Measure.pi (fun _ : Fin m × Fin (time k) => μ)
  let E (k : ℕ) : Set (Fin m × Fin (time k) → G) :=
    {w | ∀ i, ‖D (word (fun j => w (i,j)))-a‖ < δ ∧
      ‖D ((word (fun j => w (i,j)))⁻¹)-b‖ < δ}
  obtain ⟨η,hη,N,hN⟩ := endpoint_mass_eventually μ hsym D C hD z hz hc a b ha hb δ hδ
  have hmass : ∀ᶠ k in atTop, η^m ≤ (ν k).real (E k) := by
    filter_upwards [htime.eventually (eventually_ge_atTop N)] with k hk
    rw [show (ν k).real (E k) =
        ((Measure.pi (fun _ : Fin (time k) => μ)).real
          {w | ‖D (word w)-a‖ < δ ∧ ‖D ((word w)⁻¹)-b‖ < δ})^m from
      rows_event_mass μ m (time k)
        {w | ‖D (word w)-a‖ < δ ∧ ‖D ((word w)⁻¹)-b‖ < δ}]
    exact pow_le_pow_left₀ hη.le (hN _ hk) m
  let B (k : ℕ) : I ⊕ ((Fin m × Bool) × List (Fin m × Bool)) →
      Set (Fin m × Fin (time k) → G)
    | Sum.inl q => {w | δ ≤ obs q (fun i => word (fun j => w (i,j)))}
    | Sum.inr v => {w | δ ≤ ‖D (evalList (fun i => word (fun j => w (i,j))) (v.1::v.2)) -
        D (signed v.1.2 (word (fun j => w (v.1.1,j))))‖}
  have hbad (q) (hq : q ∈ Q.disjSum V) :
      Tendsto (fun k => (ν k).real (B k q)) atTop (nhds 0) := by
    cases q with
    | inl q => exact hmom q (Finset.inl_mem_disjSum.mp hq)
    | inr v =>
      have hv := hV v (Finset.inr_mem_disjSum.mp hq)
      have hbound (k : ℕ) : (ν k).real (B k (.inr v)) ≤
          (∫ ω, ‖z ω-D (walk (time k) ω)‖^2 ∂pathMeasure μ)/δ^2 := by
        let f (w : Fin m × Fin (time k) → G) :=
          D (evalList (fun i => word (fun j => w (i,j))) (v.1::v.2)) -
            D (signed v.1.2 (word (fun j => w (v.1.1,j))))
        have hf : MemLp f 2 (ν k) := MemLp.of_bound
          StronglyMeasurable.of_discrete.aestronglyMeasurable (C+C)
          (Eventually.of_forall fun w => (norm_sub_le _ _).trans (add_le_add (hD _) (hD _)))
        exact (HochschildProbability.norm_error_mass (ν k) f hf hδ).trans
          (div_le_div_of_nonneg_right (list_cauchy_bound μ hsym D z hc v.1 v.2 hv) (sq_nonneg _))
      apply squeeze_zero (fun k => measureReal_nonneg) hbound
      simpa using (hz.comp htime).div_const (δ^2)
  obtain ⟨k,w,hwE,hwB⟩ := (HochschildProbability.finite_requirements_eventually ν E
    (pow_pos hη m) hmass (Q.disjSum V) B hbad).exists
  refine ⟨fun i => word (fun j => w (i,j)), hwE, ?_, ?_⟩
  · intro q hq
    exact lt_of_not_ge (hwB (.inl q) (Finset.inl_mem_disjSum.mpr hq))
  · intro v hv
    exact lt_of_not_ge (hwB (.inr v) (Finset.inr_mem_disjSum.mpr hv))

end HochschildWalk

open Filter Topology
namespace HochschildFiniteTests

theorem finite_alphabet (F : Finset ℕ) :
    ∃ r : ℕ, 0 < r ∧ ∃ c : ℕ → Fin r, ∀ i ∈ F, (c i : ℕ) = i := by
  let r := F.sup id + 1
  have hr : 0 < r := Nat.succ_pos _
  refine ⟨r, hr, fun i => ⟨i % r, Nat.mod_lt i hr⟩, ?_⟩
  intro i hi
  exact Nat.mod_eq_of_lt (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))

lemma map_back_word {r : ℕ} (c : ℕ → Fin r) (g : FreeGroup ℕ)
    (hc : ∀ p ∈ g.toWord, (c p.1 : ℕ) = p.1) :
    FreeGroup.map (fun i : Fin r => (i : ℕ)) (FreeGroup.map c g) = g := by
  have he : (g.toWord.map (fun p => (c p.1,p.2))).map
      (fun p : Fin r × Bool => ((p.1 : ℕ),p.2)) = g.toWord := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id g.toWord]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply, hc p hp, id_eq]
  conv_lhs => rw [← FreeGroup.mk_toWord (x := g)]
  rw [FreeGroup.map.mk, FreeGroup.map.mk, he, FreeGroup.mk_toWord]

lemma map_ne_one {r : ℕ} (c : ℕ → Fin r) (g : FreeGroup ℕ)
    (hc : ∀ p ∈ g.toWord, (c p.1 : ℕ) = p.1) (hg : g ≠ 1) :
    FreeGroup.map c g ≠ 1 := by
  intro h
  apply hg
  rw [← map_back_word c g hc, h, map_one]

lemma map_nodup {r : ℕ} (c : ℕ → Fin r) (l : List (ℕ × Bool))
    (hc : ∀ p ∈ l, (c p.1 : ℕ) = p.1) (hl : (l.map Prod.fst).Nodup) :
    ((l.map (fun p => (c p.1,p.2))).map Prod.fst).Nodup := by
  have hinj : ∀ i ∈ l.map Prod.fst, ∀ j ∈ l.map Prod.fst, c i = c j → i = j := by
    intro i hi j hj he
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hi
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hj
    have hv := congrArg Fin.val he
    simpa only [hc p hp, hc q hq] using hv
  simpa only [List.map_map, Function.comp_def] using List.Nodup.map_on hinj hl

lemma lift_map {α β G : Type*} [Group G] (f : α → β) (u : β → G) (g : FreeGroup α) :
    FreeGroup.lift u (FreeGroup.map f g) = FreeGroup.lift (u ∘ f) g := by
  have he : (FreeGroup.lift u).comp (FreeGroup.map f) = FreeGroup.lift (u ∘ f) := by
    ext i
    simp
  exact DFunLike.congr_fun he g

theorem countable_constraints {X I : Type*} [Nonempty I] [Countable I]
    (P : I → Prop) (E : I → X → ℝ) (hE : ∀ i x, 0 ≤ E i x)
    (R : ℝ → X → Prop)
    (hfinite : ∀ (s : Finset I) (δ : ℝ), 0 < δ →
      ∃ x : X, R δ x ∧ ∀ i ∈ s, P i → E i x < δ) :
    ∃ x : ℕ → X, (∀ n : ℕ, R (1/(n+1:ℝ)) (x n)) ∧
      ∀ i, P i → Tendsto (fun n => E i (x n)) atTop (nhds 0) := by
  classical
  obtain ⟨enum,henum⟩ := exists_surjective_nat I
  have hex (n : ℕ) : ∃ x : X, R (1/(n+1:ℝ)) x ∧
      ∀ i ∈ (Finset.range (n+1)).image enum, P i → E i x < 1/(n+1:ℝ) :=
    hfinite _ _ (by positivity)
  choose x hx using hex
  refine ⟨x, fun n => (hx n).1, ?_⟩
  intro i hi
  obtain ⟨k,rfl⟩ := henum i
  apply squeeze_zero' (Eventually.of_forall fun n => hE _ _)
    (g := fun n : ℕ => 1/(n+1:ℝ))
  · filter_upwards [eventually_ge_atTop k] with n hn
    exact ((hx n).2 _ (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩) hi).le
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

end HochschildFiniteTests

open MeasureTheory ProbabilityTheory Filter Topology
namespace HochschildWalk
open HochschildFiniteTests
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
variable {H : Type*} [NormedAddCommGroup H]

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma evalList_map {I J : Type*} (c : I → J) (u : J → G) (l : List (I × Bool)) :
    evalList u (l.map (fun p => (c p.1,p.2))) = evalList (u ∘ c) l := by
  simp [evalList, List.map_map, Function.comp_def]

theorem finite_countable_selection (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (z : Lp H 2 (pathMeasure μ))
    (hz : Tendsto (fun k => ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ) atTop (𝓝 0))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    (a b : H) (ha : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-a‖ < r})
    (hb : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-b‖ < r})
    (φ : G → ℝ) (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (hmom : FreeMomentsInProbability μ φ time)
    (Q : Finset (FreeGroup ℕ)) (hQ : ∀ q ∈ Q, q ≠ 1)
    (V : Finset ((ℕ × Bool) × List (ℕ × Bool)))
    (hV : ∀ v ∈ V, ((v.1::v.2).map Prod.fst).Nodup)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ u : ℕ → G,
      (∀ i, ‖D (u i)-a‖ < δ ∧ ‖D ((u i)⁻¹)-b‖ < δ) ∧
      (∀ q ∈ Q, φ (FreeGroup.lift u q) < δ) ∧
      ∀ v ∈ V, ‖D (evalList u (v.1::v.2))-D (signed v.1.2 (u v.1.1))‖ < δ := by
  classical
  let F := Q.biUnion (fun q => (q.toWord.map Prod.fst).toFinset) ∪
    V.biUnion (fun v => ((v.1::v.2).map Prod.fst).toFinset)
  obtain ⟨r,hr,c,hcF⟩ := finite_alphabet F
  have hcQ (q) (hq : q ∈ Q) (p) (hp : p ∈ q.toWord) : (c p.1 : ℕ) = p.1 := by
    apply hcF
    apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨q,hq,List.mem_toFinset.mpr (List.mem_map.mpr ⟨p,hp,rfl⟩)⟩
  have hcV (v) (hv : v ∈ V) (p) (hp : p ∈ v.1::v.2) : (c p.1 : ℕ) = p.1 := by
    apply hcF
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨v,hv,List.mem_toFinset.mpr (List.mem_map.mpr ⟨p,hp,rfl⟩)⟩
  let clip : ((ℕ × Bool) × List (ℕ × Bool)) → ((Fin r × Bool) × List (Fin r × Bool)) :=
    fun v => ((c v.1.1,v.1.2), v.2.map (fun p => (c p.1,p.2)))
  have hclip (v) (hv : v ∈ V.image clip) : ((v.1::v.2).map Prod.fst).Nodup := by
    obtain ⟨v',hv',rfl⟩ := Finset.mem_image.mp hv
    exact map_nodup c (v'.1::v'.2) (hcV v' hv') (hV v' hv')
  have hobs (q) (hq : q ∈ Q) := hmom r (FreeGroup.map c q)
    (map_ne_one c q (hcQ q hq) (hQ q hq)) δ hδ
  obtain ⟨u,hu,hq,hv⟩ := finite_walk_selection μ hsym D C hD z hz hc a b ha hb r Q
    (fun q u => φ (FreeGroup.lift u (FreeGroup.map c q))) (V.image clip) hclip time htime δ hδ hobs
  refine ⟨u ∘ c, fun i => hu (c i), ?_, ?_⟩
  · intro q hqQ
    simpa only [lift_map] using hq q hqQ
  · intro v hvV
    have hh := hv (clip v) (Finset.mem_image.mpr ⟨v,hvV,rfl⟩)
    change ‖D (evalList u ((v.1::v.2).map (fun p => (c p.1,p.2)))) -
      D (signed v.1.2 (u (c v.1.1)))‖ < δ at hh
    rw [evalList_map] at hh
    exact hh

theorem infinite_walk_selection (hsym : μ.map (fun g => g⁻¹) = μ)
    (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (z : Lp H 2 (pathMeasure μ))
    (hz : Tendsto (fun k => ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ) atTop (𝓝 0))
    (hc : ∀ k n, k ≤ n → ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ)
    (a b : H) (ha : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-a‖ < r})
    (hb : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-b‖ < r})
    (φ : G → ℝ) (hφ : ∀ g, 0 ≤ φ g) (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (hmom : FreeMomentsInProbability μ φ time) :
    ∃ u : ℕ → ℕ → G,
      (∀ n i, ‖D (u n i)-a‖ < 1/(n+1:ℝ) ∧ ‖D ((u n i)⁻¹)-b‖ < 1/(n+1:ℝ)) ∧
      (∀ q : FreeGroup ℕ, q ≠ 1 → Tendsto (fun n => φ (FreeGroup.lift (u n) q)) atTop (nhds 0)) ∧
      ∀ v : ((ℕ × Bool) × List (ℕ × Bool)), ((v.1::v.2).map Prod.fst).Nodup →
        Tendsto (fun n => ‖D (evalList (u n) (v.1::v.2))-D (signed v.1.2 (u n v.1.1))‖)
          atTop (nhds 0) := by
  classical
  let I := FreeGroup ℕ ⊕ ((ℕ × Bool) × List (ℕ × Bool))
  let P : I → Prop
    | .inl q => q ≠ 1
    | .inr v => ((v.1::v.2).map Prod.fst).Nodup
  let E : I → (ℕ → G) → ℝ
    | .inl q, u => φ (FreeGroup.lift u q)
    | .inr v, u => ‖D (evalList u (v.1::v.2))-D (signed v.1.2 (u v.1.1))‖
  let R : ℝ → (ℕ → G) → Prop := fun δ u =>
    ∀ i, ‖D (u i)-a‖ < δ ∧ ‖D ((u i)⁻¹)-b‖ < δ
  have hE (i : I) (u : ℕ → G) : 0 ≤ E i u := by
    cases i with
    | inl q => exact hφ _
    | inr v => exact norm_nonneg _
  have hf (s : Finset I) (δ : ℝ) (hδ : 0 < δ) :
      ∃ u, R δ u ∧ ∀ i ∈ s, P i → E i u < δ := by
    let Q := s.toLeft.filter (fun q => q ≠ 1)
    let V := s.toRight.filter (fun v => ((v.1::v.2).map Prod.fst).Nodup)
    obtain ⟨u,hu,hq,hv⟩ := finite_countable_selection μ hsym D C hD z hz hc a b ha hb
      φ time htime hmom Q (fun _ h => (Finset.mem_filter.mp h).2)
      V (fun _ h => (Finset.mem_filter.mp h).2) δ hδ
    refine ⟨u,hu,?_⟩
    intro i hi hPi
    cases i with
    | inl q => exact hq q (Finset.mem_filter.mpr ⟨Finset.mem_toLeft.mpr hi,hPi⟩)
    | inr v => exact hv v (Finset.mem_filter.mpr ⟨Finset.mem_toRight.mpr hi,hPi⟩)
  obtain ⟨u,hu,hall⟩ := countable_constraints P E hE R hf
  exact ⟨u,hu,fun q hq => hall (.inl q) hq, fun v hv => hall (.inr v) hv⟩
end HochschildWalk
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildLiouville
open HochschildRigidity HochschildWalk HochschildFirstLetter TracialUltrapower
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))

include htr in
lemma trace_norm_unitary_right (a : A) (u : unitary A) :
    ‖τ.toPreGNS (a*(u:A))‖ = ‖τ.toPreGNS a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  push_cast
  simp only [τ.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS, star_mul]
  calc
    τ ((star (u:A)*star a)*(a*(u:A))) = τ (star (u:A)*((star a*a)*(u:A))) := by
      simp only [mul_assoc]
    _ = τ (((star a*a)*(u:A))*star (u:A)) := htr _ _
    _ = τ (star a*a) := by rw [mul_assoc, Unitary.mul_star_self_of_mem u.property, mul_one]

variable {G : Type*} [Group G]
variable (ρ : G →* unitary A) (R : A →L[ℂ] A)

omit [PartialOrder A] [StarOrderedRing A] in
lemma algebraD_mul (g : G) : algebraD ρ R g * (ρ g : A) = R (ρ g : A) := by
  simp [algebraD, mul_assoc, ← Submonoid.coe_mul]

omit [PartialOrder A] [StarOrderedRing A] in
lemma algebraD_norm (g : G) : ‖algebraD ρ R g‖ ≤ ‖R‖ * ‖(1:A)‖ := by
  rw [algebraD, CStarRing.norm_mul_coe_unitary]
  have hu := CStarRing.norm_coe_unitary_mul (ρ g) (1:A)
  simp only [mul_one] at hu
  exact (R.le_opNorm _).trans_eq (by rw [hu])

lemma hilbertD_norm (g : G) : ‖hilbertD τ h1 ρ R g‖ ≤ ‖R‖ * ‖(1:A)‖ :=
  (hilbertMap_norm τ h1 _).le.trans ((preGNS_norm_le τ h1 _).trans (algebraD_norm ρ R g))

include htr in
lemma multiplied_error (g : G) (a : A) :
    ‖τ.toPreGNS (R (ρ g : A)-a*(ρ g : A))‖ =
      ‖hilbertD τ h1 ρ R g - hilbertMap τ h1 a‖ := by
  rw [hilbertD, ← map_sub, hilbertMap_norm]
  rw [← trace_norm_unitary_right τ htr (algebraD ρ R g-a) (ρ g)]
  rw [sub_mul, algebraD_mul]

def endpointSequence (g : ℕ → G) : ℕ →ᵇ A :=
  BoundedContinuousFunction.mkOfBound ⟨fun n => algebraD ρ R (g n), continuous_of_discreteTopology⟩
    (2*(‖R‖*‖(1:A)‖)) (fun i j => by
      rw [dist_eq_norm]
      change ‖algebraD ρ R (g i)-algebraD ρ R (g j)‖ ≤ _
      exact (norm_sub_le _ _).trans (by linarith [algebraD_norm ρ R (g i), algebraD_norm ρ R (g j)]))

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma endpointSequence_apply (g : ℕ → G) (n : ℕ) :
    endpointSequence ρ R g n = algebraD ρ R (g n) := rfl

omit [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] in
lemma evalList_eq_lift {I : Type*} [DecidableEq I] (u : I → G) (g : FreeGroup I) :
    evalList u g.toWord = FreeGroup.lift u g := by
  conv_rhs => rw [← FreeGroup.mk_toWord (x := g), FreeGroup.lift_mk]
  apply congrArg List.prod
  apply List.map_congr_left
  intro p _
  cases p.2 <;> rfl

omit [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] in
lemma lift_comp_hom {J K : Type*} [Group K] (f : G →* K) (u : J → G) (g : FreeGroup J) :
    (FreeGroup.lift (fun i => f (u i))) g = f (FreeGroup.lift u g) := by
  have he : FreeGroup.lift (fun i => f (u i)) = f.comp (FreeGroup.lift u) := by
    ext i
    simp
  exact DFunLike.congr_fun he g

variable [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]

include htr

theorem support_rigidity (hR : BallSequential τ.toPreGNS R)
    (hsym : μ.map (fun g => g⁻¹) = μ)
    (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (hmom : FreeMomentsInProbability μ (fun g => ‖τ (ρ g : A)‖) time)
    (z : Lp τ.GNS 2 (pathMeasure μ))
    (hz : Tendsto (fun k => ∫ ω, ‖z ω-hilbertD τ h1 ρ R (walk k ω)‖^2 ∂pathMeasure μ) atTop (𝓝 0))
    (hc : ∀ k n, k ≤ n →
      ∫ ω, ‖hilbertD τ h1 ρ R (walk n ω)-hilbertD τ h1 ρ R (walk k ω)‖^2 ∂pathMeasure μ ≤
      ∫ ω, ‖z ω-hilbertD τ h1 ρ R (walk k ω)‖^2 ∂pathMeasure μ)
    (a b : τ.GNS) (ha : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-a‖ < r})
    (hb : ∀ r > 0, 0 < (pathMeasure μ).real {ω | ‖z ω-b‖ < r}) : a = b := by
  obtain ⟨u,hu,hfree,hblock⟩ := infinite_walk_selection μ hsym (hilbertD τ h1 ρ R)
    (‖R‖*‖(1:A)‖) (hilbertD_norm τ h1 ρ R) z hz hc a b ha hb
    (fun g => ‖τ (ρ g : A)‖) (fun _ => norm_nonneg _) time htime hmom
  let U (n : ℕ) : FreeGroup ℕ →* unitary A := FreeGroup.lift (fun i => ρ (u n i))
  let a' := endpointSequence ρ R (fun n => u n 0)
  let b' := endpointSequence ρ R (fun n => (u n 0)⁻¹)
  have ha' : Tendsto (fun n => hilbertMap τ h1 (a' n)) atTop (nhds a) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hu n 0).1.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hb' : Tendsto (fun n => hilbertMap τ h1 (b' n)) atTop (nhds b) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hu n 0).2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hw (g : FreeGroup ℕ) (i : ℕ) (t : Bool) (l : List (ℕ × Bool))
      (hg : g.toWord = (i,t)::l) (hn : (g.toWord.map Prod.fst).Nodup) :
      Tendsto (fun n => ‖τ.toPreGNS (R (U n g : A) - (if t then a' n else b' n)*(U n g : A))‖)
        atTop (nhds 0) := by
    have he := hblock ((i,t),l) (by simpa only [hg] using hn)
    have hnear : Tendsto (fun n =>
        ‖hilbertD τ h1 ρ R (signed t (u n i)) -
          hilbertMap τ h1 (if t then a' n else b' n)‖) atTop (nhds 0) := by
      cases t with
      | false =>
        have hi : Tendsto (fun n => hilbertD τ h1 ρ R ((u n i)⁻¹)) atTop (nhds b) := by
          rw [tendsto_iff_norm_sub_tendsto_zero]
          exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hu n i).2.le)
            tendsto_one_div_add_atTop_nhds_zero_nat
        simpa only [signed, Bool.false_eq_true, ↓reduceIte, sub_self, norm_zero] using (hi.sub hb').norm
      | true =>
        have hi : Tendsto (fun n => hilbertD τ h1 ρ R (u n i)) atTop (nhds a) := by
          rw [tendsto_iff_norm_sub_tendsto_zero]
          exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hu n i).1.le)
            tendsto_one_div_add_atTop_nhds_zero_nat
        simpa only [signed, ↓reduceIte, sub_self, norm_zero] using (hi.sub ha').norm
    have hzero := he.add hnear
    simp only [zero_add] at hzero
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hzero
    change ‖τ.toPreGNS (R (FreeGroup.lift (fun i => ρ (u n i)) g : A) - _ * _)‖ ≤ _
    rw [lift_comp_hom, multiplied_error τ h1 htr]
    have hword : evalList (u n) ((i,t)::l) = FreeGroup.lift (u n) g := by
      rw [← hg, evalList_eq_lift]
    rw [hword]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hab := asymptotic_first_letter_endpoints τ h1 htr R hR U
    (fun g hg => by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [U, lift_comp_hom] using hfree g hg) a' b' hw
  have hh : Tendsto (fun n => ‖τ.toPreGNS (a' n-b' n)‖) atTop (nhds ‖a-b‖) := by
    simpa only [← map_sub, hilbertMap_norm] using (ha'.sub hb').norm
  exact sub_eq_zero.mp (norm_eq_zero.mp (tendsto_nhds_unique hh hab))

end HochschildLiouville

open MeasureTheory Filter Topology TopologicalSpace
namespace HochschildProbability

theorem ae_constant_of_support_unique {Ω H : Type*} [MeasurableSpace Ω] [Nonempty Ω]
    [NormedAddCommGroup H] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → H) (hf : AEStronglyMeasurable f μ)
    (huniq : ∀ a b : H,
      (∀ r > 0, 0 < μ.real {ω | ‖f ω-a‖ < r}) →
      (∀ r > 0, 0 < μ.real {ω | ‖f ω-b‖ < r}) → a = b) :
    ∃ a : H, ∀ᵐ ω ∂μ, f ω = a := by
  classical
  by_contra hn
  have hn' (b : H) : ¬ ∀ᵐ ω ∂μ, f ω = b := fun h => hn ⟨b,h⟩
  let f' := hf.mk f
  let S := Set.range f'
  have : SeparableSpace S := hf.stronglyMeasurable_mk.isSeparable_range.separableSpace
  have : Nonempty S := ⟨⟨f' (Classical.arbitrary Ω), ⟨_,rfl⟩⟩⟩
  let g : Ω → S := fun ω => ⟨f' ω, ⟨ω,rfl⟩⟩
  have hg : ∀ b : S, ∃ᵐ ω ∂μ, g ω ≠ b := by
    intro b
    apply Filter.not_eventually.mp
    intro hb
    apply hn' b.val
    filter_upwards [hf.ae_eq_mk, hb] with ω he hb
    exact he.trans (congrArg Subtype.val hb)
  obtain ⟨a,b,hab,ha,hb⟩ := exists_ne_forall_mem_nhds_pos_measure_preimage hg
  have hs (x : S) (hx : ∀ s ∈ 𝓝 x, 0 < μ (g ⁻¹' s)) :
      ∀ r > 0, 0 < μ.real {ω | ‖f ω-x.val‖ < r} := by
    intro r hr
    have hp := hx (Metric.ball x r) (Metric.ball_mem_nhds x hr)
    have he : μ {ω | ‖f ω-x.val‖ < r} = μ (g ⁻¹' Metric.ball x r) := by
      apply measure_congr
      filter_upwards [hf.ae_eq_mk] with ω hω
      change (‖f ω-x.val‖ < r) = (dist (g ω) x < r)
      rw [Subtype.dist_eq, dist_eq_norm]
      change (‖f ω-x.val‖ < r) = (‖f' ω-x.val‖ < r)
      rw [hω]
    rw [Measure.real, he]
    exact ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  exact hab (Subtype.ext (huniq a.val b.val (hs a ha) (hs b hb)))

end HochschildProbability

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal
namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma processLp_const_inner (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C)
    (hh : ∀ g, ∫ u, D (g*u) ∂μ = D g) (n : ℕ) (c : H) :
    inner ℝ (processLp μ D C hD n-processLp μ D C hD 0)
      (Lp.const 2 (pathMeasure μ) c) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : inner ℝ (processLp μ D C hD (n+1)-processLp μ D C hD n)
        (Lp.const 2 (pathMeasure μ) c) = 0 := by
      rw [L2.inner_def]
      have he := increment_inner_integral μ D C hD hh n (fun _ => c) ‖c‖ (fun _ => le_rfl)
      refine Eq.trans (integral_congr_ae ?_) he
      filter_upwards [Lp.coeFn_sub (processLp μ D C hD (n+1)) (processLp μ D C hD n),
        processLp_ae μ D C hD (n+1), processLp_ae μ D C hD n,
        Lp.coeFn_const 2 (pathMeasure μ) c] with ω hs hn hn' hc
      rw [hs,Pi.sub_apply,hn,hn',hc]
      rfl
    have he : processLp μ D C hD (n+1)-processLp μ D C hD 0 =
        (processLp μ D C hD (n+1)-processLp μ D C hD n) +
          (processLp μ D C hD n-processLp μ D C hD 0) := by abel
    rw [he,inner_add_left,hstep,ih,add_zero]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma processLp_zero (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) :
    processLp μ D C hD 0 = Lp.const 2 (pathMeasure μ) (D 1) := by
  apply Lp.ext
  filter_upwards [processLp_ae μ D C hD 0, Lp.coeFn_const 2 (pathMeasure μ) (D 1)] with ω he hc
  simp only [he,hc,walk,word,List.ofFn_zero,List.prod_nil,Function.const_apply]

theorem atoms_eq_of_constant_limit (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C)
    (hh : ∀ g, ∫ u, D (g*u) ∂μ = D g)
    (z : Lp H 2 (pathMeasure μ)) (hz : Tendsto (fun n => processLp μ D C hD n) atTop (nhds z))
    (c : H) (hc : ∀ᵐ ω ∂pathMeasure μ, z ω = c) :
    ∀ g, μ {g} ≠ 0 → D g = D 1 := by
  let Z := processLp μ D C hD
  have hzconst : z = Lp.const 2 (pathMeasure μ) c := by
    apply Lp.ext
    filter_upwards [hc, Lp.coeFn_const 2 (pathMeasure μ) c] with ω hω hconst
    exact hω.trans hconst.symm
  have hdiff : Lp.const 2 (pathMeasure μ) (c-D 1) = z-Z 0 := by
    rw [map_sub,hzconst,show Z 0 = _ from processLp_zero μ D C hD]
  have hlim := ((hz.sub_const (Z 0)).inner tendsto_const_nhds :
    Tendsto (fun n => inner ℝ (Z n-Z 0) (Lp.const 2 (pathMeasure μ) (c-D 1)))
      atTop (nhds (inner ℝ (z-Z 0) (Lp.const 2 (pathMeasure μ) (c-D 1)))))
  have hzero : inner ℝ (z-Z 0) (Lp.const 2 (pathMeasure μ) (c-D 1)) = 0 :=
    tendsto_nhds_unique hlim (by simpa only [Z,processLp_const_inner μ D C hD hh] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (nhds 0)))
  rw [hdiff,real_inner_self_eq_norm_sq] at hzero
  have heq : z = Z 0 := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hzero))
  obtain ⟨z',hz',_,hbound⟩ := HochschildMartingale.uniform_cauchy_error Z
    (fun _ _ h => processLp_orthogonal μ D C hD hh h) C (processLp_norm_le μ D C hD)
  have heq' : z' = Z 0 := (tendsto_nhds_unique hz' hz).trans heq
  have hZ1 : Z 1 = Z 0 := by
    have hb := hbound 0 1 (by omega)
    rw [heq',sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hb
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hb (sq_nonneg _))))
  have hpath : ∀ᵐ ω ∂pathMeasure μ, D (ω 0) = D 1 := by
    have hae := Lp.ext_iff.mp hZ1
    filter_upwards [hae,processLp_ae μ D C hD 1,processLp_ae μ D C hD 0] with ω he h1 h0
    change processLp μ D C hD 1 ω = processLp μ D C hD 0 ω at he
    rw [h1,h0] at he
    simpa [walk,word,takePath,List.ofFn_succ] using he
  have hg : ∀ᵐ g ∂μ, D g = D 1 := by
    have hm : (pathMeasure μ).map (Function.eval 0) = μ :=
      Measure.infinitePi_map_eval (fun _ : ℕ => μ) 0
    rw [← hm]
    exact (ae_map_iff (measurable_pi_apply 0).aemeasurable (Set.to_countable _).measurableSet).mpr hpath
  exact ae_iff_of_countable.mp hg

end HochschildWalk

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildLiouville
open HochschildRigidity HochschildWalk HochschildFirstLetter TracialUltrapower
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
variable (hf : ∀ x : A, τ (star x * x) = 0 → x = 0)
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (ρ : G →* unitary A) (R : A →L[ℂ] A)
variable (μ : Measure G) [IsProbabilityMeasure μ]

include htr hf

theorem atoms_multiplier (hR : BallSequential τ.toPreGNS R)
    (hsym : μ.map (fun g => g⁻¹) = μ)
    (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (hmom : FreeMomentsInProbability μ (fun g => ‖τ (ρ g : A)‖) time)
    (hh : ∀ g, ∫ u, hilbertD τ h1 ρ R (g*u) ∂μ = hilbertD τ h1 ρ R g) :
    ∀ g, μ {g} ≠ 0 → R (ρ g : A) = R 1 * (ρ g : A) := by
  let : InnerProductSpace ℝ τ.GNS := InnerProductSpace.rclikeToReal ℂ τ.GNS
  obtain ⟨z,hz,he,hc⟩ := harmonic_mean_square_convergence μ (hilbertD τ h1 ρ R)
    (‖R‖*‖(1:A)‖) (hilbertD_norm τ h1 ρ R) hh
  obtain ⟨a,ha⟩ := HochschildProbability.ae_constant_of_support_unique (pathMeasure μ) z
    (Lp.aestronglyMeasurable z) (support_rigidity τ h1 htr ρ R μ hR hsym time htime hmom z he hc)
  have hatom := atoms_eq_of_constant_limit μ (hilbertD τ h1 ρ R)
    (‖R‖*‖(1:A)‖) (hilbertD_norm τ h1 ρ R) hh z hz a ha
  intro g hg
  have he := hatom g hg
  have hn : ‖τ.toPreGNS (algebraD ρ R g-algebraD ρ R 1)‖ = 0 := by
    rw [← hilbertMap_norm τ h1, map_sub]
    change ‖hilbertD τ h1 ρ R g-hilbertD τ h1 ρ R 1‖ = 0
    rw [he, sub_self, norm_zero]
  have heq := sub_eq_zero.mp ((preGNS_norm_eq_zero_iff τ hf _).mp hn)
  have heq' := congrArg (fun x : A => x*(ρ g : A)) heq
  rw [algebraD_mul] at heq'
  simpa [algebraD] using heq'
end HochschildLiouville
end
end OAI
end

theorem solution.{u_1,u_2} : type_of% @OAI.HochschildLiouville.atoms_multiplier.{u_1,u_2} := @OAI.HochschildLiouville.atoms_multiplier.{u_1,u_2}
