-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T16:59:26.1806+00:00
-- url     : https://prove2.me/submissions/175b9361-92d5-45bb-9d54-287c3e3373d8

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_UniqueGamesTheorem
import Definitions.Def_OAIQ086U009

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_FiberEnergyLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Energy after merging a bounded number of frequencies

This finite ordered-ring theorem supplies the Cauchy–Schwarz step in (A.10).
Its fiber-cardinality hypothesis is explicit.
-/

namespace UniqueGamesTheorem.Appendix.FiberEnergy

open scoped BigOperators

variable {α β R : Type*} [Fintype β] [DecidableEq β] [CommRing R] [LinearOrder R]
  [IsStrictOrderedRing R]

/-- The energy of a sum of merged coefficients is bounded by the largest
fiber size times the original coefficient energy. Signs and cancellations
are unrestricted; no injectivity assumption is made. -/
theorem finite_fiber_energy (s : Finset α) (compress : α → β) (a : α → R)
    (bound : R) (hbound : ∀ z,
      ((s.filter (fun y => compress y = z)).card : R) ≤ bound) :
    (∑ z, (∑ y ∈ s.filter (fun y => compress y = z), a y) ^ 2) ≤
      bound * ∑ y ∈ s, a y ^ 2 := by
  classical
  have hlocal (z : β) :
      (∑ y ∈ s.filter (fun y => compress y = z), a y) ^ 2 ≤
        bound * ∑ y ∈ s.filter (fun y => compress y = z), a y ^ 2 := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq
      (s.filter (fun y => compress y = z)) (fun _ => (1 : R)) a
    calc
      _ ≤ ((s.filter (fun y => compress y = z)).card : R) *
          ∑ y ∈ s.filter (fun y => compress y = z), a y ^ 2 := by simpa using hc
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound z)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  calc
    _ ≤ ∑ z, bound * ∑ y ∈ s.filter (fun y => compress y = z), a y ^ 2 :=
      Finset.sum_le_sum (fun z _ => hlocal z)
    _ = bound * ∑ y ∈ s, a y ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise]

end UniqueGamesTheorem.Appendix.FiberEnergy

end

section

/-! Finite Gram-energy estimates used in Lemma A.1. -/
namespace UniqueGamesTheorem.Appendix.F1Gram
open scoped BigOperators

/-- The squared entries of a Gram matrix are bounded by the squared total
energy of its underlying rows. This is a pairwise Cauchy–Schwarz argument. -/
theorem gram_energy_le {R C : Type*} [Fintype R] [Fintype C] (p : R → C → ℝ) :
    (∑ r, ∑ s, (∑ c, p r c * p s c)^2) ≤
      (∑ r, ∑ c, p r c^2)^2 := by
  classical
  let e : R → ℝ := fun r => ∑ c, p r c^2
  calc
    _ ≤ ∑ r, ∑ s, e r * e s := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro s _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (p r) (p s)
    _ = (∑ r, e r) * (∑ s, e s) := (Finset.sum_mul_sum _ _ _ _).symm
    _ = (∑ r, ∑ c, p r c^2)^2 := (pow_two _).symm

theorem sum_subtype_eq {A : Type*} [Fintype A] (P : A → Prop)
    [DecidablePred P] (f : A → ℝ) :
    (∑ x : {x // P x}, f x) = ∑ x : A, if P x then f x else 0 := by
  classical
  calc
    _ = ∑ x ∈ Finset.univ.filter P, f x := by
      refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
      · intro x _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩
      · intro x _ y _ h
        exact Subtype.ext h
      · intro y hy
        exact ⟨⟨y, (Finset.mem_filter.mp hy).2⟩, Finset.mem_univ _, rfl⟩
      · intro x _
        rfl
    _ = _ := by rw [Finset.sum_filter]

theorem sum_comp_le {A B : Type*} [Fintype A] [Fintype B] (e : A → B)
    (he : Function.Injective e) (f : B → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ a, f (e a)) ≤ ∑ b, f b := by
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image e, f b :=
      (Finset.sum_image (fun a _ b _ h => he h)).symm
    _ ≤ ∑ b ∈ Finset.univ, f b := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun b _ _ => hf b)

end UniqueGamesTheorem.Appendix.F1Gram

end

section

namespace UniqueGamesTheorem.Appendix.Induction

theorem square_remainder_budget (d t : Nat) (ht : t ≤ d) :
    (d - t) * (d - t) + d * t ≤ d * d := by
  have hm := Nat.mul_le_mul_left (d - t) (Nat.sub_le d t)
  have hs : d - t + t = d := by omega
  have he : (d - t) * d + t * d = d * d := by
    rw [← Nat.add_mul, hs]
  rw [Nat.mul_comm d t]
  omega

/-- The exponent inequality preceding (A.16), with negative exponents moved
to the left side so natural subtraction cannot hide an invalid inequality. -/
theorem induction_exponent_budget (d t k : Nat) (ht : t ≤ d) (hk : k ≤ t) :
    100 * ((d - t) * (d - t)) + 27 * (d * t) + 6 * (d * k) +
      63 * (d * t) + 4 * (d * k) ≤ 100 * (d * d) := by
  have hs := Nat.mul_le_mul_left 100 (square_remainder_budget d t ht)
  have hm := Nat.mul_le_mul_left d hk
  omega

theorem antecedent_exponent_budget (d i j k t : Nat)
    (ht : t = i + j + k) (hd : t ≤ d) :
    d * (i + j) + 2 * (d * k) + k * k ≤ 3 * (d * t) := by
  have hk : k ≤ d := by omega
  have hm := Nat.mul_le_mul_right k hk
  have he : d * t = d * (i + j) + d * k := by
    rw [ht, Nat.mul_add]
  omega

/-- For positive k the geometric-series exponent has at least d of slack. -/
theorem positive_rank_geometric_slack (d k : Nat) (hk : 1 ≤ k) :
    31 * (d * (k + 1)) + d ≤ 63 * (d * k) := by
  have hm := Nat.mul_le_mul_left d hk
  have he : d * (k + 1) = d * k + d := by simp [Nat.mul_add]
  omega

end UniqueGamesTheorem.Appendix.Induction

end

section

namespace UniqueGamesTheorem.Appendix.Level.LinearRank

open Module LinearMap
attribute [local instance] Classical.propDecidable

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V] [FiniteDimensional K W] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem quotient_rank_selected (A : Submodule K V) (Y : W →ₗ[K] V)
    (hA : A ≤ range Y) :
    finrank K (range (A.mkQ.comp Y)) + finrank K A = finrank K (range Y) := by
  have h := (A.mkQ.comp (range Y).subtype).finrank_range_add_finrank_ker
  have hr : range (A.mkQ.comp (range Y).subtype) = range (A.mkQ.comp Y) := by
    simp only [range_comp, Submodule.range_subtype]
  rw [hr, ker_comp, Submodule.ker_mkQ,
    (Submodule.comapSubtypeEquivOfLe hA).finrank_eq] at h
  exact h

omit [FiniteDimensional K V] in
theorem domain_rank_selected (B : Submodule K W) (Y : W →ₗ[K] V)
    (hB : ker Y ≤ B) :
    finrank K (range (Y.comp B.subtype)) + finrank K (W ⧸ B) =
      finrank K (range Y) := by
  have h₁ := (Y.comp B.subtype).finrank_range_add_finrank_ker
  have h₂ := Y.finrank_range_add_finrank_ker
  have h₃ := B.finrank_quotient_add_finrank
  rw [ker_comp, (Submodule.comapSubtypeEquivOfLe hB).finrank_eq] at h₁
  omega

omit [FiniteDimensional K V] in
theorem hybrid_rank_loss (A : Submodule K V) (B : Submodule K W)
    (Y : W →ₗ[K] V) (hA : A ≤ range Y) (hB : A.comap Y ≤ B) :
    finrank K (range (compress A B Y)) + finrank K A + finrank K (W ⧸ B) =
      finrank K (range Y) := by
  have hquot := quotient_rank_selected A Y hA
  have hdom := domain_rank_selected B (A.mkQ.comp Y) (by
    simpa only [ker_comp, Submodule.ker_mkQ] using hB)
  have hc : (A.mkQ.comp Y).comp B.subtype = compress A B Y := rfl
  rw [hc] at hdom
  omega

end UniqueGamesTheorem.Appendix.Level.LinearRank

end

section

/-!
# Rank-additive pairs of linear maps

The rank-additive selector in Appendix A.1 has a concrete geometric meaning:
the two image spaces are disjoint and the two kernels span the domain. These
lemmas apply over any field and arbitrary finite dimensions, in particular
over `ZMod 2` with the second map equal to `Y + X`.
-/

namespace UniqueGamesTheorem.Appendix.RankAdditivity

open Module LinearMap

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

variable [FiniteDimensional K W]

theorem rankBelow_iff (X Y : W →ₗ[K] V) :
    RankBelow X Y ↔
      Disjoint (LinearMap.range X) (LinearMap.range (Y - X)) ∧
        LinearMap.ker X ⊔ LinearMap.ker (Y - X) = ⊤ := by
  have h := finrank_add_eq_iff X (Y - X)
  rw [add_remainder] at h
  exact h

theorem range_remainder_eq_range_on_kernel (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.range (Y - X) = LinearMap.range (Y.domRestrict (LinearMap.ker X)) := by
  have hc := ((rankBelow_iff X Y).mp h).2
  apply le_antisymm
  · rintro v ⟨w, hw⟩
    have ht : w ∈ LinearMap.ker X ⊔ LinearMap.ker (Y - X) := by rw [hc]; trivial
    rcases Submodule.mem_sup.mp ht with ⟨k, hk, j, hj, hkj⟩
    have hzk : (Y - X) k = (Y - X) w := by
      rw [← hkj, map_add, show (Y - X) j = 0 from hj, add_zero]
    refine ⟨⟨k, hk⟩, ?_⟩
    change Y k = v
    calc
      Y k = (Y - X) k := by
        change Y k = Y k - X k
        rw [show X k = 0 from hk, sub_zero]
      _ = (Y - X) w := hzk
      _ = v := hw
  · rintro v ⟨w, hw⟩
    refine ⟨(w : W), ?_⟩
    change Y w - X w = v
    rw [show X w = 0 from w.property, sub_zero]
    exact hw

theorem mem_ker_of_apply_mem_range_remainder (X Y : W →ₗ[K] V)
    (h : RankBelow X Y) (w : W) (hw : Y w ∈ LinearMap.range (Y - X)) :
    w ∈ LinearMap.ker X := by
  have hd := ((rankBelow_iff X Y).mp h).1
  have hz : (Y - X) w ∈ LinearMap.range (Y - X) := ⟨w, rfl⟩
  have hx : X w ∈ LinearMap.range (Y - X) := by
    have hs := (LinearMap.range (Y - X)).sub_mem hw hz
    have heq : Y w - (Y - X) w = X w := by
      simp only [LinearMap.sub_apply]
      abel
    exact heq ▸ hs
  exact Submodule.disjoint_def.mp hd (X w) ⟨w, rfl⟩ hx

end UniqueGamesTheorem.Appendix.RankAdditivity

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_DegreeCover
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The arbitrary-dimensional linear-algebra cover in Appendix A.1. -/
namespace UniqueGamesTheorem.Appendix.DegreeCover

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

/-- Glue a linear map on P to zero on Q when the restrictions agree. -/
theorem exists_glue_zero (P Q : Submodule F2 W) (f : W →ₗ[F2] V)
    (cover : P ⊔ Q = ⊤) (compatible : ∀ w ∈ P, w ∈ Q → f w = 0) :
    ∃ g : W →ₗ[F2] V,
      (∀ w ∈ P, g w = f w) ∧ (∀ w ∈ Q, g w = 0) := by
  let p : W →ₗ.[F2] V := ⟨P, f.comp P.subtype⟩
  let q : W →ₗ.[F2] V := ⟨Q, 0⟩
  have hc : ∀ (x : p.domain) (y : q.domain), (x : W) = y → p x = q y := by
    intro x y hxy
    exact compatible x x.property (hxy ▸ y.property)
  let t := p.sup q hc
  have ht : ∀ w : W, w ∈ t.domain := by
    intro w
    change w ∈ P ⊔ Q
    rw [cover]
    exact Submodule.mem_top
  let inc : W →ₗ[F2] t.domain := (LinearMap.id : W →ₗ[F2] W).codRestrict t.domain ht
  refine ⟨t.toFun.comp inc, ?_, ?_⟩
  · intro w hw
    exact ((p.left_le_sup q hc).2 (x := ⟨w, hw⟩) (y := inc w) rfl).symm
  · intro w hw
    exact ((p.right_le_sup q hc).2 (x := ⟨w, hw⟩) (y := inc w) rfl).symm

private theorem binary_cross {a b c d : V} (h : a + b = c + d) : c + a = d + b := by
  calc
    c + a = (c + a) + (b + b) := by simp
    _ = c + (a + b) + b := by abel
    _ = c + (c + d) + b := by rw [h]
    _ = (c + c) + (d + b) := by abel
    _ = d + b := by simp

theorem exists_cover_component (Y Z : W →ₗ[F2] V)
    (triple : (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z = ⊥)
    (cover : LinearMap.ker (Y + Z) ⊔ LinearMap.ker Y ⊔ LinearMap.ker Z = ⊤) :
    ∃ R : W →ₗ[F2] V,
      (∀ w ∈ LinearMap.ker Z, R w = Y w) ∧
      (∀ w ∈ LinearMap.ker Y ⊔ LinearMap.ker (Y + Z), R w = 0) ∧
      LinearMap.range R ≤ LinearMap.range (Y + Z) ⊓ LinearMap.range Y := by
  have cov : LinearMap.ker Z ⊔ (LinearMap.ker Y ⊔ LinearMap.ker (Y + Z)) = ⊤ := by
    simpa only [sup_assoc, sup_comm, sup_left_comm] using cover
  have compatible : ∀ w ∈ LinearMap.ker Z,
      w ∈ LinearMap.ker Y ⊔ LinearMap.ker (Y + Z) → Y w = 0 := by
    intro w hw hz
    change Z w = 0 at hw
    rcases Submodule.mem_sup.mp hz with ⟨a, ha, b, hb, hab⟩
    change Y a = 0 at ha
    change (Y + Z) b = 0 at hb
    have hYb : Y b = Z b := by
      have h := congrArg (fun v : V => v + Z b) hb
      simpa only [LinearMap.add_apply, add_assoc, binary_add_self, add_zero, zero_add] using h
    have hYw : Y w = Z b := by rw [← hab, map_add, ha, zero_add, hYb]
    have hmem : Y w ∈ (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z :=
      ⟨⟨⟨w, by simp only [LinearMap.add_apply, hw, add_zero]⟩, ⟨w, rfl⟩⟩,
        ⟨b, hYw.symm⟩⟩
    rw [triple] at hmem
    exact hmem
  obtain ⟨R, hRZ, hRYX⟩ := exists_glue_zero (LinearMap.ker Z)
    (LinearMap.ker Y ⊔ LinearMap.ker (Y + Z)) Y cov compatible
  refine ⟨R, hRZ, hRYX, ?_⟩
  rintro v ⟨w, rfl⟩
  have hw : w ∈ LinearMap.ker Z ⊔ (LinearMap.ker Y ⊔ LinearMap.ker (Y + Z)) := by
    rw [cov]
    exact Submodule.mem_top
  rcases Submodule.mem_sup.mp hw with ⟨a, ha, b, hb, hab⟩
  have heq : R w = Y a := by rw [← hab, map_add, hRZ a ha, hRYX b hb, add_zero]
  refine ⟨⟨a, ?_⟩, ⟨a, heq.symm⟩⟩
  change Z a = 0 at ha
  rw [LinearMap.add_apply, ha, add_zero, heq]

/-- A general, dimension-free decomposition with pairwise disjoint images.
These are exactly the linear-algebra data used to establish the cover in A.1. -/
theorem exists_disjoint_decomposition (Y Z : W →ₗ[F2] V)
    (triple : (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z = ⊥)
    (cover : LinearMap.ker (Y + Z) ⊔ LinearMap.ker Y ⊔ LinearMap.ker Z = ⊤) :
    ∃ R S C : W →ₗ[F2] V,
      Y + Z = R + S ∧ Y = R + C ∧ Z = S + C ∧
      Disjoint (LinearMap.range R) (LinearMap.range S) ∧
      Disjoint (LinearMap.range R) (LinearMap.range C) ∧
      Disjoint (LinearMap.range S) (LinearMap.range C) ∧
      LinearMap.range R ≤ LinearMap.range (Y + Z) ⊓ LinearMap.range Y ∧
      LinearMap.range S ≤ LinearMap.range (Y + Z) ⊓ LinearMap.range Z ∧
      LinearMap.range C ≤ LinearMap.range Y ⊓ LinearMap.range Z := by
  obtain ⟨R, hRZ, hRYX, rangeR⟩ := exists_cover_component Y Z triple cover
  obtain ⟨S, hSY, hSZX, rangeS⟩ := exists_cover_component Z Y
    (by simpa only [add_comm Z Y, inf_assoc, inf_comm, inf_left_comm] using triple)
    (by simpa only [add_comm Z Y, sup_assoc, sup_comm, sup_left_comm] using cover)
  rw [add_comm Z Y] at hSZX rangeS
  have eqX : Set.EqOn (R + S) (Y + Z) (LinearMap.ker (Y + Z)) := by
    intro w hw
    change (R + S) w = (Y + Z) w
    rw [LinearMap.add_apply, hRYX w (Submodule.mem_sup_right hw), hSZX w (Submodule.mem_sup_right hw)]
    simpa only [zero_add] using hw.symm
  have eqY : Set.EqOn (R + S) (Y + Z) (LinearMap.ker Y) := by
    intro w hw
    change (R + S) w = (Y + Z) w
    change Y w = 0 at hw
    simp only [LinearMap.add_apply, hRYX w (Submodule.mem_sup_left hw), hSY w hw, hw, zero_add]
  have eqZ : Set.EqOn (R + S) (Y + Z) (LinearMap.ker Z) := by
    intro w hw
    change (R + S) w = (Y + Z) w
    change Z w = 0 at hw
    simp only [LinearMap.add_apply, hRZ w hw, hSZX w (Submodule.mem_sup_left hw), hw, add_zero]
  have hRS : R + S = Y + Z := by
    ext w
    exact LinearMap.eqOn_sup (LinearMap.eqOn_sup eqX eqY) eqZ (cover ▸ Submodule.mem_top)
  let C := Y + R
  have hC : C = Z + S := by
    ext w
    exact binary_cross (congrArg (fun f : W →ₗ[F2] V => f w) hRS)
  have hY : Y = R + C := by
    ext w
    change Y w = R w + (Y w + R w)
    rw [add_left_comm, binary_add_self, add_zero]
  have hZ : Z = S + C := by
    rw [hC]
    ext w
    change Z w = S w + (Z w + S w)
    rw [add_left_comm, binary_add_self, add_zero]
  have rangeC : LinearMap.range C ≤ LinearMap.range Y ⊓ LinearMap.range Z := by
    apply le_inf
    · exact (LinearMap.range_add_le Y R).trans (sup_le le_rfl (rangeR.trans inf_le_right))
    · rw [hC]
      exact (LinearMap.range_add_le Z S).trans (sup_le le_rfl (rangeS.trans inf_le_right))
  have kill : ∀ v, v ∈ LinearMap.range (Y + Z) → v ∈ LinearMap.range Y →
      v ∈ LinearMap.range Z → v = 0 := by
    intro v hx hy hz
    have h : v ∈ (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z := ⟨⟨hx, hy⟩, hz⟩
    rwa [triple] at h
  refine ⟨R, S, C, hRS.symm, hY, hZ, ?_, ?_, ?_, rangeR, rangeS, rangeC⟩
  · exact Submodule.disjoint_def.mpr (fun v hr hs => kill v (rangeR hr).1 (rangeR hr).2 (rangeS hs).2)
  · exact Submodule.disjoint_def.mpr (fun v hr hc => kill v (rangeR hr).1 (rangeR hr).2 (rangeC hc).2)
  · exact Submodule.disjoint_def.mpr (fun v hs hc => kill v (rangeS hs).1 (rangeC hc).1 (rangeS hs).2)

/-- Rank additivity needs image containment as well as disjointness. -/
theorem rank_add_of_disjoint [FiniteDimensional F2 V] (R S : W →ₗ[F2] V)
    (hd : Disjoint (LinearMap.range R) (LinearMap.range S))
    (hR : LinearMap.range R ≤ LinearMap.range (R + S))
    (hS : LinearMap.range S ≤ LinearMap.range (R + S)) :
    Module.finrank F2 (LinearMap.range (R + S)) =
      Module.finrank F2 (LinearMap.range R) + Module.finrank F2 (LinearMap.range S) := by
  have heq := le_antisymm (LinearMap.range_add_le R S) (sup_le hR hS)
  rw [heq]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range R) (LinearMap.range S)
  have hb : LinearMap.range R ⊓ LinearMap.range S = ⊥ := hd.eq_bot
  rw [hb, finrank_bot, add_zero] at h
  exact h

/-- The cover F(X) \ F₂(X) ⊆ F₁(X), with all three rank-additive decompositions.
There is no bound on dimension, and both bad-event exclusions are discharged. -/
theorem outside_bad_rank_cover [FiniteDimensional F2 V] (Y Z : W →ₗ[F2] V)
    (triple : (LinearMap.range (Y + Z) ⊓ LinearMap.range Y) ⊓ LinearMap.range Z = ⊥)
    (cover : LinearMap.ker (Y + Z) ⊔ LinearMap.ker Y ⊔ LinearMap.ker Z = ⊤) :
    ∃ R S C : W →ₗ[F2] V,
      Y + Z = R + S ∧ Y = R + C ∧ Z = S + C ∧
      Module.finrank F2 (LinearMap.range (Y + Z)) =
        Module.finrank F2 (LinearMap.range R) + Module.finrank F2 (LinearMap.range S) ∧
      Module.finrank F2 (LinearMap.range Y) =
        Module.finrank F2 (LinearMap.range R) + Module.finrank F2 (LinearMap.range C) ∧
      Module.finrank F2 (LinearMap.range Z) =
        Module.finrank F2 (LinearMap.range S) + Module.finrank F2 (LinearMap.range C) := by
  obtain ⟨R, S, C, hX, hY, hZ, dRS, dRC, dSC, rR, rS, rC⟩ :=
    exists_disjoint_decomposition Y Z triple cover
  refine ⟨R, S, C, hX, hY, hZ, ?_, ?_, ?_⟩
  · rw [hX]
    exact rank_add_of_disjoint R S dRS
      (hX ▸ rR.trans inf_le_left) (hX ▸ rS.trans inf_le_left)
  · rw [hY]
    exact rank_add_of_disjoint R C dRC
      (hY ▸ rR.trans inf_le_right) (hY ▸ rC.trans inf_le_left)
  · rw [hZ]
    exact rank_add_of_disjoint S C dSC
      (hZ ▸ rS.trans inf_le_right) (hZ ▸ rC.trans inf_le_right)

end UniqueGamesTheorem.Appendix.DegreeCover

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_Identities
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.LinearIdentities

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

theorem compress_sub (X Y : W →ₗ[K] V) (A : Submodule K V) (B : Submodule K W) :
    compress (Y - X) A B = compress Y A B - compress X A B := by
  ext b
  simp only [compress_apply, LinearMap.sub_apply, map_sub]

theorem quotient_mem_image_iff (A₀ A : Submodule K V) (hA : A₀ ≤ A) (v : V) :
    A₀.mkQ v ∈ A.map A₀.mkQ ↔ v ∈ A := by
  change v ∈ (A.map A₀.mkQ).comap A₀.mkQ ↔ v ∈ A
  rw [Submodule.comap_map_mkQ, sup_of_le_right hA]

/-- The exact nested-selector equivalence of (A.3), now using Mathlib's
linear maps, submodules, restriction, and quotient construction. -/
theorem nested_hybrid_iff (Y : W →ₗ[K] V) (A₀ A : Submodule K V)
    (B B₀ : Submodule K W) (hA : A₀ ≤ A) (hB : B ≤ B₀) :
    (Hybrid Y A₀ B₀ ∧
      Hybrid (compress Y A₀ B₀) (A.map A₀.mkQ) (B.comap B₀.subtype)) ↔
    Hybrid Y A B := by
  constructor
  · rintro ⟨inner, outer⟩
    constructor
    · intro a ha
      have hqa : A₀.mkQ a ∈ A.map A₀.mkQ := ⟨a, ha, rfl⟩
      rcases outer.1 hqa with ⟨b, hb⟩
      have hdiff : Y b - a ∈ A₀ :=
        (Submodule.Quotient.eq A₀).mp hb
      rcases inner.1 hdiff with ⟨c, hc⟩
      refine ⟨(b : W) - c, ?_⟩
      rw [map_sub, hc]
      abel
    · intro w hw
      have hqa : A₀.mkQ (Y w) ∈ A.map A₀.mkQ := ⟨Y w, hw, rfl⟩
      rcases outer.1 hqa with ⟨b, hb⟩
      have hdiff : Y w - Y b ∈ A₀ :=
        (Submodule.Quotient.eq A₀).mp hb.symm
      have hwb : w - b ∈ B₀ := inner.2 (by
        change Y (w - b) ∈ A₀
        simpa only [map_sub] using hdiff)
      have hw₀ : w ∈ B₀ := by
        have h := B₀.add_mem hwb b.property
        simpa only [sub_add_cancel] using h
      have hout : (⟨w, hw₀⟩ : B₀) ∈ (A.map A₀.mkQ).comap (compress Y A₀ B₀) := hqa
      exact outer.2 hout
  · intro full
    constructor
    · exact ⟨hA.trans full.1, (Submodule.comap_mono hA).trans (full.2.trans hB)⟩
    · constructor
      · intro q hq
        rcases hq with ⟨a, ha, rfl⟩
        rcases full.1 ha with ⟨w, hw⟩
        have hwB : w ∈ B := full.2 (by
          change Y w ∈ A
          rw [hw]
          exact ha)
        refine ⟨⟨w, hB hwB⟩, ?_⟩
        simp only [compress_apply, hw]
      · intro b hb
        have hYb : Y b ∈ A := (quotient_mem_image_iff A₀ A hA (Y b)).mp hb
        exact full.2 hYb

variable [FiniteDimensional K W]

/-- Compression preserves the full rank when its quotient is disjoint
from the image and its restricted domain spans the domain modulo the kernel. -/
theorem compress_rank_preserved (X : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hdis : Disjoint A (LinearMap.range X))
    (hcover : B ⊔ LinearMap.ker X = ⊤) :
    Module.finrank K (LinearMap.range (compress X A B)) =
      Module.finrank K (LinearMap.range X) := by
  have hrestrict : LinearMap.range (X.domRestrict B) = LinearMap.range X := by
    apply le_antisymm (LinearMap.range_domRestrict_le_range X B)
    intro v hv
    rcases hv with ⟨w, hw⟩
    have hwtop : w ∈ B ⊔ LinearMap.ker X := by rw [hcover]; trivial
    rcases Submodule.mem_sup.mp hwtop with ⟨b, hb, k, hk, hbk⟩
    refine ⟨⟨b, hb⟩, ?_⟩
    change X b = v
    rw [← hw, ← hbk, map_add, show X k = 0 from hk, add_zero]
  have h := (A.mkQ.comp (LinearMap.range X).subtype).finrank_range_add_finrank_ker
  have hr : LinearMap.range (A.mkQ.comp (LinearMap.range X).subtype) =
      LinearMap.range (compress X A B) := by
    simp only [compress, LinearMap.range_comp, Submodule.range_subtype, hrestrict]
  rw [hr, LinearMap.ker_comp, Submodule.ker_mkQ,
    Submodule.disjoint_iff_comap_eq_bot.mp hdis.symm] at h
  simpa using h

/-- The reverse summand of (A.5) really satisfies the hybrid selector for
the remainder `Y - X`. The hypotheses here are exactly the inner hybrid
selector, complement conditions, and the compressed rank-order selector.
No image-lifting or disjointness conclusion is assumed separately. -/
theorem reverse_hybrid_of_compressed_rankBelow (X Y : W →ₗ[K] V)
    (A₀ : Submodule K V) (B₀ : Submodule K W)
    (inner : Hybrid Y A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hlocal : RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀)) :
    Hybrid (Y - X) A₀ B₀ := by
  have hker := RankAdditivity.ker_le_of_rankBelow
    (compress X A₀ B₀) (compress Y A₀ B₀) hlocal
  have himg := RankAdditivity.range_le_of_rankBelow
    (compress X A₀ B₀) (compress Y A₀ B₀) hlocal
  constructor
  · intro a ha
    rcases inner.1 ha with ⟨w, hw⟩
    have hwB : w ∈ B₀ := inner.2 (by change Y w ∈ A₀; rw [hw]; exact ha)
    have hwy : (⟨w, hwB⟩ : B₀) ∈ LinearMap.ker (compress Y A₀ B₀) := by
      change Y w ∈ LinearMap.ker A₀.mkQ
      rw [Submodule.ker_mkQ, hw]
      exact ha
    have hxA : X w ∈ A₀ := by
      have hx : X w ∈ LinearMap.ker A₀.mkQ := hker hwy
      simpa only [Submodule.ker_mkQ] using hx
    have hx : X w = 0 := Submodule.disjoint_def.mp hdis (X w) hxA ⟨w, rfl⟩
    exact ⟨w, by change Y w - X w = a; rw [hw, hx, sub_zero]⟩
  · intro w hw
    have hwZ : Y w - X w ∈ A₀ := hw
    have hwtop : w ∈ B₀ ⊔ LinearMap.ker X := by rw [hcover]; trivial
    rcases Submodule.mem_sup.mp hwtop with ⟨b, hb, k, hk, hbk⟩
    have hxb : X b = X w := by
      rw [← hbk, map_add, show X k = 0 from hk, add_zero]
    have hxran : compress X A₀ B₀ ⟨b, hb⟩ ∈ LinearMap.range (compress X A₀ B₀) :=
      ⟨⟨b, hb⟩, rfl⟩
    rcases himg hxran with ⟨c, hc⟩
    have hdiff : X w - Y c ∈ A₀ := by
      rw [← hxb]
      exact (Submodule.Quotient.eq A₀).mp hc.symm
    have hsum : Y (w - c) ∈ A₀ := by
      have h := A₀.add_mem hwZ hdiff
      have heq : (Y w - X w) + (X w - Y c) = Y (w - c) := by rw [map_sub]; abel
      exact heq ▸ h
    have hwc : w - c ∈ B₀ := inner.2 hsum
    have h := B₀.add_mem hwc c.property
    simpa only [sub_add_cancel] using h

/-- A surviving right-hand summand of (A.5) forces the original rank
order `X ⪯ Y`. This lifts the local rank equation using the two actual
hybrid rank-loss equalities, so it does not assume global rank additivity. -/
theorem rankBelow_of_compressed_rankBelow (X Y : W →ₗ[K] V)
    (A₀ : Submodule K V) (B₀ : Submodule K W)
    (inner : Hybrid Y A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hlocal : RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀)) :
    RankAdditivity.RankBelow X Y := by
  have remainder := reverse_hybrid_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have hY := Level.LinearRank.hybrid_rank_loss A₀ B₀ Y inner.1 inner.2
  have hZ := Level.LinearRank.hybrid_rank_loss A₀ B₀ (Y - X) remainder.1 remainder.2
  have hX := compress_rank_preserved X A₀ B₀ hdis hcover
  change Module.finrank K (LinearMap.range (compress Y A₀ B₀)) +
    Module.finrank K A₀ + Module.finrank K (W ⧸ B₀) = Module.finrank K (LinearMap.range Y) at hY
  change Module.finrank K (LinearMap.range (compress (Y - X) A₀ B₀)) +
    Module.finrank K A₀ + Module.finrank K (W ⧸ B₀) = Module.finrank K (LinearMap.range (Y - X)) at hZ
  have hloc : Module.finrank K (LinearMap.range (compress Y A₀ B₀)) =
      Module.finrank K (LinearMap.range (compress X A₀ B₀)) +
      Module.finrank K (LinearMap.range (compress (Y - X) A₀ B₀)) := by
    rw [compress_sub]
    exact hlocal
  change Module.finrank K (LinearMap.range Y) = Module.finrank K (LinearMap.range X) +
    Module.finrank K (LinearMap.range (Y - X))
  omega

/-- The complement in the codomain is forced by the remainder image. -/
theorem image_inter_complement_eq (A₀ I J : Submodule K V)
    (hA : A₀ ≤ J) (hdis : Disjoint I J) : J ⊓ (A₀ ⊔ I) = A₀ := by
  apply le_antisymm
  · intro v hv
    rcases Submodule.mem_sup.mp hv.2 with ⟨a, ha, i, hi, hai⟩
    have hiJ : i ∈ J := by
      have h := J.sub_mem hv.1 (hA ha)
      have heq : v - a = i := by rw [← hai]; abel
      exact heq ▸ h
    have hi0 := Submodule.disjoint_def.mp hdis i hi hiJ
    rw [hi0, add_zero] at hai
    exact hai ▸ ha
  · intro a ha
    exact ⟨hA ha, (show A₀ ≤ A₀ ⊔ I from le_sup_left) ha⟩

omit [FiniteDimensional K W] in
/-- The complement in the domain is forced by the remainder kernel. -/
theorem domain_complement_eq (B₀ K₀ J : Submodule K W)
    (hJ : J ≤ B₀) (hcover : K₀ ⊔ J = ⊤) : B₀ = (B₀ ⊓ K₀) ⊔ J := by
  apply le_antisymm
  · intro w hw
    have hwtop : w ∈ K₀ ⊔ J := by rw [hcover]; trivial
    rcases Submodule.mem_sup.mp hwtop with ⟨k, hk, j, hj, hkj⟩
    have hkB : k ∈ B₀ := by
      have h := B₀.sub_mem hw (hJ hj)
      have heq : w - j = k := by rw [← hkj]; abel
      exact heq ▸ h
    exact Submodule.mem_sup.mpr ⟨k, ⟨hkB, hk⟩, j, hj, hkj⟩
  · exact sup_le inf_le_left hJ

/-- Every surviving right-hand pair in (A.5) is the displayed canonical pair. -/
theorem surviving_pair_forced (X Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (inner : Hybrid Y A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hA : A₀ ⊔ LinearMap.range X = A)
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hB : B₀ ⊓ LinearMap.ker X = B)
    (hlocal : RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀)) :
    A₀ = LinearMap.range (Y - X) ⊓ A ∧ B₀ = B ⊔ LinearMap.ker (Y - X) := by
  have remainder := reverse_hybrid_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have global := rankBelow_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have geometry := (RankAdditivity.rankBelow_iff X Y).mp global
  constructor
  · have h := image_inter_complement_eq A₀ (LinearMap.range X)
      (LinearMap.range (Y - X)) remainder.1 geometry.1
    rw [hA] at h
    exact h.symm
  · have hker : LinearMap.ker (Y - X) ≤ B₀ := by
      intro w hw
      apply remainder.2
      change (Y - X) w ∈ A₀
      rw [show (Y - X) w = 0 from hw]
      exact A₀.zero_mem
    have h := domain_complement_eq B₀ (LinearMap.ker X) (LinearMap.ker (Y - X)) hker geometry.2
    rw [hB] at h
    exact h

theorem canonical_inner_hybrid (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hrank : RankAdditivity.RankBelow X Y)
    (outer : Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) :
    Hybrid Y (LinearMap.range (Y - X) ⊓ A) (B ⊔ LinearMap.ker (Y - X)) := by
  constructor
  · have hz : LinearMap.range (Y - X) ≤ LinearMap.range Y := by
      rw [RankAdditivity.range_remainder_eq_range_on_kernel X Y hrank]
      exact LinearMap.range_domRestrict_le_range Y (LinearMap.ker X)
    exact inf_le_left.trans hz
  · intro w hw
    have hy : Y w ∈ LinearMap.range (Y - X) ⊓ A := hw
    have hk : w ∈ LinearMap.ker X :=
      RankAdditivity.mem_ker_of_apply_mem_range_remainder X Y hrank w hy.1
    have hq : (⟨w, hk⟩ : LinearMap.ker X) ∈
        (A.map (LinearMap.range X).mkQ).comap
          (compress Y (LinearMap.range X) (LinearMap.ker X)) :=
      ⟨Y w, hy.2, rfl⟩
    have hb : w ∈ B := outer.2 hq
    exact (show B ≤ B ⊔ LinearMap.ker (Y - X) from le_sup_left) hb

theorem canonical_remainder_hybrid (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hrank : RankAdditivity.RankBelow X Y)
    (outer : Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) :
    Hybrid (Y - X) (LinearMap.range (Y - X) ⊓ A) (B ⊔ LinearMap.ker (Y - X)) := by
  constructor
  · exact inf_le_left
  · intro w hw
    have hwZ : (Y - X) w ∈ LinearMap.range (Y - X) ⊓ A := hw
    have hc := ((RankAdditivity.rankBelow_iff X Y).mp hrank).2
    have ht : w ∈ LinearMap.ker X ⊔ LinearMap.ker (Y - X) := by rw [hc]; trivial
    rcases Submodule.mem_sup.mp ht with ⟨k, hk, j, hj, hkj⟩
    have hzk : (Y - X) k = (Y - X) w := by
      rw [← hkj, map_add, show (Y - X) j = 0 from hj, add_zero]
    have hyk : Y k = (Y - X) w := by
      calc
        Y k = (Y - X) k := by
          change Y k = Y k - X k
          rw [show X k = 0 from hk, sub_zero]
        _ = (Y - X) w := hzk
    have hyA : Y k ∈ A := by rw [hyk]; exact hwZ.2
    have hq : (⟨k, hk⟩ : LinearMap.ker X) ∈
        (A.map (LinearMap.range X).mkQ).comap
          (compress Y (LinearMap.range X) (LinearMap.ker X)) :=
      ⟨Y k, hyA, rfl⟩
    have hkB : k ∈ B := outer.2 hq
    exact Submodule.mem_sup.mpr ⟨k, hkB, j, hj, hkj⟩

theorem canonical_codomain_complement (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hI : LinearMap.range X ≤ A) (hrank : RankAdditivity.RankBelow X Y)
    (outer : Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) :
    Disjoint (LinearMap.range (Y - X) ⊓ A) (LinearMap.range X) ∧
      (LinearMap.range (Y - X) ⊓ A) ⊔ LinearMap.range X = A := by
  have hd := ((RankAdditivity.rankBelow_iff X Y).mp hrank).1
  refine ⟨hd.symm.mono_left inf_le_left, ?_⟩
  apply le_antisymm (sup_le inf_le_right hI)
  intro a ha
  have hqa : (LinearMap.range X).mkQ a ∈ A.map (LinearMap.range X).mkQ := ⟨a, ha, rfl⟩
  rcases outer.1 hqa with ⟨k, hk⟩
  have hi : a - Y k ∈ LinearMap.range X :=
    (Submodule.Quotient.eq (LinearMap.range X)).mp hk.symm
  have hyA : Y k ∈ A := by
    have h := A.sub_mem ha (hI hi)
    have heq : a - (a - Y k) = Y k := by abel
    exact heq ▸ h
  have hyZ : Y k ∈ LinearMap.range (Y - X) :=
    ⟨(k : W), by
      change Y k - X k = Y k
      rw [show X k = 0 from k.property, sub_zero]⟩
  exact Submodule.mem_sup.mpr ⟨Y k, ⟨hyZ, hyA⟩, a - Y k, hi, by abel⟩

theorem canonical_domain_complement (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hB : B ≤ LinearMap.ker X) (hrank : RankAdditivity.RankBelow X Y)
    (outer : Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) :
    (B ⊔ LinearMap.ker (Y - X)) ⊓ LinearMap.ker X = B ∧
      (B ⊔ LinearMap.ker (Y - X)) ⊔ LinearMap.ker X = ⊤ := by
  constructor
  · apply le_antisymm
    · intro w hw
      rcases Submodule.mem_sup.mp hw.1 with ⟨b, hb, j, hj, hbj⟩
      have hjK : j ∈ LinearMap.ker X := by
        have h := (LinearMap.ker X).sub_mem hw.2 (hB hb)
        have heq : w - b = j := by rw [← hbj]; abel
        exact heq ▸ h
      have hyj : Y j = 0 := by
        have hz : Y j - X j = 0 := hj
        rw [show X j = 0 from hjK, sub_zero] at hz
        exact hz
      have hq : (⟨j, hjK⟩ : LinearMap.ker X) ∈
          (A.map (LinearMap.range X).mkQ).comap
            (compress Y (LinearMap.range X) (LinearMap.ker X)) := by
        change (LinearMap.range X).mkQ (Y j) ∈ A.map (LinearMap.range X).mkQ
        rw [hyj, map_zero]
        exact Submodule.zero_mem _
      have hjB : j ∈ B := outer.2 hq
      have h := B.add_mem hb hjB
      exact hbj ▸ h
    · exact le_inf le_sup_left hB
  · have hc := ((RankAdditivity.rankBelow_iff X Y).mp hrank).2
    calc
      (B ⊔ LinearMap.ker (Y - X)) ⊔ LinearMap.ker X =
        B ⊔ (LinearMap.ker X ⊔ LinearMap.ker (Y - X)) := by ac_rfl
      _ = ⊤ := by rw [hc, sup_top_eq]

theorem compressed_rankBelow_of_hybrids (X Y : W →ₗ[K] V)
    (A₀ : Submodule K V) (B₀ : Submodule K W)
    (hy : Hybrid Y A₀ B₀) (hz : Hybrid (Y - X) A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hrank : RankAdditivity.RankBelow X Y) :
    RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀) := by
  have hY := Level.LinearRank.hybrid_rank_loss A₀ B₀ Y hy.1 hy.2
  have hZ := Level.LinearRank.hybrid_rank_loss A₀ B₀ (Y - X) hz.1 hz.2
  have hX := compress_rank_preserved X A₀ B₀ hdis hcover
  change Module.finrank K (LinearMap.range (compress Y A₀ B₀)) +
    Module.finrank K A₀ + Module.finrank K (W ⧸ B₀) = Module.finrank K (LinearMap.range Y) at hY
  change Module.finrank K (LinearMap.range (compress (Y - X) A₀ B₀)) +
    Module.finrank K A₀ + Module.finrank K (W ⧸ B₀) = Module.finrank K (LinearMap.range (Y - X)) at hZ
  change Module.finrank K (LinearMap.range Y) = Module.finrank K (LinearMap.range X) +
    Module.finrank K (LinearMap.range (Y - X)) at hrank
  change Module.finrank K (LinearMap.range (compress Y A₀ B₀)) =
    Module.finrank K (LinearMap.range (compress X A₀ B₀)) +
    Module.finrank K (LinearMap.range (compress Y A₀ B₀ - compress X A₀ B₀))
  rw [← compress_sub]
  omega

theorem reverse_outer_hybrid (X Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (inner : Hybrid Y A₀ B₀)
    (hdis : Disjoint A₀ (LinearMap.range X))
    (hA : A₀ ⊔ LinearMap.range X = A)
    (hcover : B₀ ⊔ LinearMap.ker X = ⊤)
    (hB : B₀ ⊓ LinearMap.ker X = B)
    (hlocal : RankAdditivity.RankBelow (compress X A₀ B₀) (compress Y A₀ B₀)) :
    Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
      (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype) := by
  have hg := rankBelow_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have hz := reverse_hybrid_of_compressed_rankBelow X Y A₀ B₀ inner hdis hcover hlocal
  have hf := surviving_pair_forced X Y A₀ A B B₀ inner hdis hA hcover hB hlocal
  have hI : LinearMap.range X ≤ A := by rw [← hA]; exact le_sup_right
  constructor
  · intro q hq
    rcases hq with ⟨a, ha, rfl⟩
    have haSum : a ∈ A₀ ⊔ LinearMap.range X := by rw [hA]; exact ha
    rcases Submodule.mem_sup.mp haSum with ⟨a₀, ha₀, i, hi, hai⟩
    rcases inner.1 ha₀ with ⟨w, hw⟩
    have hyZ : Y w ∈ LinearMap.range (Y - X) := by rw [hw]; exact hz.1 ha₀
    have hwK : w ∈ LinearMap.ker X :=
      RankAdditivity.mem_ker_of_apply_mem_range_remainder X Y hg w hyZ
    refine ⟨⟨w, hwK⟩, ?_⟩
    have hqi : (LinearMap.range X).mkQ i = 0 := by
      change i ∈ LinearMap.ker (LinearMap.range X).mkQ
      rw [Submodule.ker_mkQ]
      exact hi
    change (LinearMap.range X).mkQ (Y w) = (LinearMap.range X).mkQ a
    rw [hw, ← hai, map_add, hqi, add_zero]
  · intro k hk
    have hyA : Y k ∈ A :=
      (quotient_mem_image_iff (LinearMap.range X) A hI (Y k)).mp hk
    have hZk : (Y - X) k = Y k := by
      change Y k - X k = Y k
      rw [show X k = 0 from k.property, sub_zero]
    have hyZ : Y k ∈ LinearMap.range (Y - X) := ⟨(k : W), hZk⟩
    have ha₀ : Y k ∈ A₀ := by rw [hf.1]; exact ⟨hyZ, hyA⟩
    have hkB₀ : (k : W) ∈ B₀ := hz.2 (by
      change (Y - X) k ∈ A₀
      rw [hZk]
      exact ha₀)
    change (k : W) ∈ B
    rw [← hB]
    exact ⟨hkB₀, k.property⟩

/-- The complete unique-summand selector identity in (A.5), in arbitrary
finite dimensions. In characteristic two the remainder `Y-X` is `Y+X`. -/
theorem a5_unique_selector (X Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (hI : LinearMap.range X ≤ A) (hB : B ≤ LinearMap.ker X) :
    (RankAdditivity.RankBelow X Y ∧
      Hybrid (compress Y (LinearMap.range X) (LinearMap.ker X))
        (A.map (LinearMap.range X).mkQ) (B.comap (LinearMap.ker X).subtype)) ↔
      ∃! p : Submodule K V × Submodule K W, A5PairSurvives X Y A B p := by
  constructor
  · rintro ⟨hr, ho⟩
    have hy := canonical_inner_hybrid X Y A B hr ho
    have hz := canonical_remainder_hybrid X Y A B hr ho
    have ha := canonical_codomain_complement X Y A B hI hr ho
    have hb := canonical_domain_complement X Y A B hB hr ho
    have hl := compressed_rankBelow_of_hybrids X Y
      (LinearMap.range (Y - X) ⊓ A) (B ⊔ LinearMap.ker (Y - X)) hy hz ha.1 hb.2 hr
    refine ⟨(LinearMap.range (Y - X) ⊓ A, B ⊔ LinearMap.ker (Y - X)),
      ⟨hy, ha.1, ha.2, hb.2, hb.1, hl⟩, ?_⟩
    rintro ⟨A₀, B₀⟩ hp
    rcases hp with ⟨hi, hd, ha', hc, hb', hl'⟩
    have hf := surviving_pair_forced X Y A₀ A B B₀ hi hd ha' hc hb' hl'
    exact Prod.ext hf.1 hf.2
  · rintro ⟨⟨A₀, B₀⟩, hp, _⟩
    rcases hp with ⟨hi, hd, ha, hc, hb, hl⟩
    exact ⟨rankBelow_of_compressed_rankBelow X Y A₀ B₀ hi hd hc hl,
      reverse_outer_hybrid X Y A₀ A B B₀ hi hd ha hc hb hl⟩

/-! ## The unique selector in (A.4) -/

theorem a4_codomain_forced (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (inner : Hybrid Y A₀ B₀)
    (hker : LinearMap.ker X = B.comap B₀.subtype)
    (himage : LinearMap.range X = A.map A₀.mkQ)
    (hlocal : RankAdditivity.RankBelow X (compress Y A₀ B₀)) :
    A₀ = (B.map Y) ⊓ A := by
  have hk := RankAdditivity.ker_le_of_rankBelow X (compress Y A₀ B₀) hlocal
  have hd := ((RankAdditivity.rankBelow_iff X (compress Y A₀ B₀)).mp hlocal).1
  apply le_antisymm
  · intro a ha
    rcases inner.1 ha with ⟨w, hw⟩
    have hwB₀ : w ∈ B₀ := inner.2 (by change Y w ∈ A₀; rw [hw]; exact ha)
    have hwy : (⟨w, hwB₀⟩ : B₀) ∈ LinearMap.ker (compress Y A₀ B₀) := by
      change Y w ∈ LinearMap.ker A₀.mkQ
      rw [Submodule.ker_mkQ, hw]
      exact ha
    have hwX := hk hwy
    rw [hker] at hwX
    exact ⟨⟨w, hwX, hw⟩, hA ha⟩
  · intro a ha
    rcases ha.1 with ⟨b, hb, hYb⟩
    let bb : B₀ := ⟨b, hB hb⟩
    have hxb : X bb = 0 := by
      have hx : bb ∈ LinearMap.ker X := by rw [hker]; exact hb
      exact hx
    have hymem : compress Y A₀ B₀ bb ∈ LinearMap.range X := by
      rw [himage]
      exact ⟨Y b, by rw [hYb]; exact ha.2, rfl⟩
    have hzmem : compress Y A₀ B₀ bb ∈ LinearMap.range (compress Y A₀ B₀ - X) :=
      ⟨bb, by change compress Y A₀ B₀ bb - X bb = compress Y A₀ B₀ bb; rw [hxb, sub_zero]⟩
    have hz := Submodule.disjoint_def.mp hd (compress Y A₀ B₀ bb) hymem hzmem
    have hm : Y b ∈ LinearMap.ker A₀.mkQ := hz
    rw [Submodule.ker_mkQ, hYb] at hm
    exact hm

theorem a4_domain_forced (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (inner : Hybrid Y A₀ B₀)
    (hker : LinearMap.ker X = B.comap B₀.subtype)
    (himage : LinearMap.range X = A.map A₀.mkQ)
    (hlocal : RankAdditivity.RankBelow X (compress Y A₀ B₀)) :
    B₀ = B ⊔ A.comap Y := by
  have hrange := RankAdditivity.range_le_of_rankBelow X (compress Y A₀ B₀) hlocal
  have hcover := ((RankAdditivity.rankBelow_iff X (compress Y A₀ B₀)).mp hlocal).2
  apply le_antisymm
  · intro w hw
    let ww : B₀ := ⟨w, hw⟩
    have ht : ww ∈ LinearMap.ker X ⊔ LinearMap.ker (compress Y A₀ B₀ - X) := by
      rw [hcover]; trivial
    rcases Submodule.mem_sup.mp ht with ⟨b, hb, p, hp, hbp⟩
    have hbB : (b : W) ∈ B := by rw [hker] at hb; exact hb
    have hpEq : compress Y A₀ B₀ p = X p := by
      have hz : compress Y A₀ B₀ p - X p = 0 := hp
      exact sub_eq_zero.mp hz
    have hq : A₀.mkQ (Y p) ∈ A.map A₀.mkQ := by
      rw [← himage]
      change compress Y A₀ B₀ p ∈ LinearMap.range X
      rw [hpEq]
      exact ⟨p, rfl⟩
    have hpA : (p : W) ∈ A.comap Y :=
      (quotient_mem_image_iff A₀ A hA (Y p)).mp hq
    exact Submodule.mem_sup.mpr ⟨(b : W), hbB, (p : W), hpA, congrArg Subtype.val hbp⟩
  · apply sup_le hB
    intro w hw
    have hqx : A₀.mkQ (Y w) ∈ LinearMap.range X := by
      rw [himage]
      exact ⟨Y w, hw, rfl⟩
    rcases hrange hqx with ⟨c, hc⟩
    have hdiff : Y w - Y c ∈ A₀ := (Submodule.Quotient.eq A₀).mp hc.symm
    have hwc : w - c ∈ B₀ := inner.2 (by
      change Y (w - c) ∈ A₀
      simpa only [map_sub] using hdiff)
    have h := B₀.add_mem hwc c.property
    simpa only [sub_add_cancel] using h

theorem a4_apply_on_preimage (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (himage : LinearMap.range X = A.map A₀.mkQ)
    (hlocal : RankAdditivity.RankBelow X (compress Y A₀ B₀))
    (p : B₀) (hp : Y p ∈ A) : X p = A₀.mkQ (Y p) := by
  have hd := ((RankAdditivity.rankBelow_iff X (compress Y A₀ B₀)).mp hlocal).1
  have hy : compress Y A₀ B₀ p ∈ LinearMap.range X := by
    rw [himage]
    exact ⟨Y p, hp, rfl⟩
  have hx : X p ∈ LinearMap.range X := ⟨p, rfl⟩
  have hzX : (compress Y A₀ B₀ - X) p ∈ LinearMap.range X :=
    (LinearMap.range X).sub_mem hy hx
  have hzR : (compress Y A₀ B₀ - X) p ∈ LinearMap.range (compress Y A₀ B₀ - X) := ⟨p, rfl⟩
  have hz := Submodule.disjoint_def.mp hd ((compress Y A₀ B₀ - X) p) hzX hzR
  exact (sub_eq_zero.mp hz).symm

theorem a4_map_unique (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X₁ X₂ : B₀ →ₗ[K] (V ⧸ A₀))
    (hA : A₀ ≤ A) (hB : B ≤ B₀) (inner : Hybrid Y A₀ B₀)
    (hk₁ : LinearMap.ker X₁ = B.comap B₀.subtype)
    (hk₂ : LinearMap.ker X₂ = B.comap B₀.subtype)
    (hi₁ : LinearMap.range X₁ = A.map A₀.mkQ)
    (hi₂ : LinearMap.range X₂ = A.map A₀.mkQ)
    (hr₁ : RankAdditivity.RankBelow X₁ (compress Y A₀ B₀))
    (hr₂ : RankAdditivity.RankBelow X₂ (compress Y A₀ B₀)) : X₁ = X₂ := by
  have hd := a4_domain_forced Y A₀ A B B₀ X₁ hA hB inner hk₁ hi₁ hr₁
  ext w
  have hw : (w : W) ∈ B ⊔ A.comap Y := by rw [← hd]; exact w.property
  rcases Submodule.mem_sup.mp hw with ⟨b, hb, p, hp, hbp⟩
  let bb : B₀ := ⟨b, hB hb⟩
  have hpB₀ : p ∈ B₀ := by rw [hd]; exact Submodule.mem_sup_right hp
  let pp : B₀ := ⟨p, hpB₀⟩
  have heq : w = bb + pp := Subtype.ext hbp.symm
  have hb₁ : X₁ bb = 0 := by
    have h : bb ∈ LinearMap.ker X₁ := by rw [hk₁]; exact hb
    exact h
  have hb₂ : X₂ bb = 0 := by
    have h : bb ∈ LinearMap.ker X₂ := by rw [hk₂]; exact hb
    exact h
  have hp₁ := a4_apply_on_preimage Y A₀ A B₀ X₁ hi₁ hr₁ pp hp
  have hp₂ := a4_apply_on_preimage Y A₀ A B₀ X₂ hi₂ hr₂ pp hp
  rw [heq, map_add, map_add, hb₁, hb₂, hp₁, hp₂]

theorem a4_weak_selector_of_summand (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀)) (inner : Hybrid Y A₀ B₀)
    (hker : LinearMap.ker X = B.comap B₀.subtype)
    (himage : LinearMap.range X = A.map A₀.mkQ)
    (hlocal : RankAdditivity.RankBelow X (compress Y A₀ B₀)) :
    A ≤ LinearMap.range Y ∧ LinearMap.ker Y ≤ B := by
  have hi := RankAdditivity.range_le_of_rankBelow X (compress Y A₀ B₀) hlocal
  have hk := RankAdditivity.ker_le_of_rankBelow X (compress Y A₀ B₀) hlocal
  constructor
  · intro a ha
    have hqa : A₀.mkQ a ∈ LinearMap.range X := by rw [himage]; exact ⟨a, ha, rfl⟩
    rcases hi hqa with ⟨c, hc⟩
    have hdiff : Y c - a ∈ A₀ := (Submodule.Quotient.eq A₀).mp hc
    rcases inner.1 hdiff with ⟨w, hw⟩
    refine ⟨(c : W) - w, ?_⟩
    rw [map_sub, hw]
    abel
  · intro w hw
    have hyw : Y w = 0 := hw
    have hwB₀ : w ∈ B₀ := inner.2 (by change Y w ∈ A₀; rw [hyw]; exact A₀.zero_mem)
    have hwq : (⟨w, hwB₀⟩ : B₀) ∈ LinearMap.ker (compress Y A₀ B₀) := by
      change A₀.mkQ (Y w) = 0
      rw [hyw, map_zero]
    have hwx := hk hwq
    rw [hker] at hwx
    exact hwx

omit [FiniteDimensional K W] in
theorem a4_kernel_of_gluing (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (hA₀ : A₀ = (B.map Y) ⊓ A) (hB₀ : B₀ = B ⊔ A.comap Y)
    (hKY : LinearMap.ker Y ≤ B)
    (hzero : ∀ b : B₀, (b : W) ∈ B → X b = 0)
    (hcopy : ∀ p : B₀, Y p ∈ A → X p = A₀.mkQ (Y p)) :
    LinearMap.ker X = B.comap B₀.subtype := by
  ext w
  constructor
  · intro hw
    have hwSum : (w : W) ∈ B ⊔ A.comap Y := by rw [← hB₀]; exact w.property
    rcases Submodule.mem_sup.mp hwSum with ⟨b, hb, p, hp, hbp⟩
    have hb₀ : b ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_left hb
    have hp₀ : p ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_right hp
    let bb : B₀ := ⟨b, hb₀⟩
    let pp : B₀ := ⟨p, hp₀⟩
    have heq : w = bb + pp := Subtype.ext hbp.symm
    have hxp : X pp = 0 := by
      have hxw : X w = 0 := hw
      rw [heq, map_add, hzero bb hb, zero_add] at hxw
      exact hxw
    have hqp : A₀.mkQ (Y p) = 0 := (hcopy pp hp).symm.trans hxp
    have hy₀ : Y p ∈ A₀ := by
      have hm : Y p ∈ LinearMap.ker A₀.mkQ := hqp
      simpa only [Submodule.ker_mkQ] using hm
    rw [hA₀] at hy₀
    rcases hy₀.1 with ⟨b', hb', hYb'⟩
    have hpk : p - b' ∈ LinearMap.ker Y := by
      change Y (p - b') = 0
      rw [map_sub, hYb', sub_self]
    have hpB : p ∈ B := by
      have h := B.add_mem (hKY hpk) hb'
      simpa only [sub_add_cancel] using h
    have h := B.add_mem hb hpB
    change (w : W) ∈ B
    exact hbp ▸ h
  · intro hw
    exact hzero w hw

theorem disjoint_quotient_images_of_intersection
    (A₀ A C : Submodule K V) (hA₀ : A₀ = C ⊓ A) :
    Disjoint (A.map A₀.mkQ) (C.map A₀.mkQ) := by
  apply Submodule.disjoint_def.mpr
  intro v hvA hvC
  rcases hvA with ⟨a, ha, hqa⟩
  rcases hvC with ⟨c, hc, hqc⟩
  have hdiff : c - a ∈ A₀ := (Submodule.Quotient.eq A₀).mp (hqc.trans hqa.symm)
  have hdiffA : c - a ∈ A := by rw [hA₀] at hdiff; exact hdiff.2
  have hcA : c ∈ A := by
    have h := A.add_mem hdiffA ha
    simpa only [sub_add_cancel] using h
  have hc₀ : c ∈ A₀ := by rw [hA₀]; exact ⟨hc, hcA⟩
  have hqzero : A₀.mkQ c = 0 := by
    change c ∈ LinearMap.ker A₀.mkQ
    rw [Submodule.ker_mkQ]
    exact hc₀
  exact hqc.symm.trans hqzero

omit [FiniteDimensional K W] in
theorem a4_range_of_gluing (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀))
    (hB₀ : B₀ = B ⊔ A.comap Y) (hAY : A ≤ LinearMap.range Y)
    (hzero : ∀ b : B₀, (b : W) ∈ B → X b = 0)
    (hcopy : ∀ p : B₀, Y p ∈ A → X p = A₀.mkQ (Y p)) :
    LinearMap.range X = A.map A₀.mkQ := by
  apply le_antisymm
  · rintro v ⟨w, hw⟩
    have hwSum : (w : W) ∈ B ⊔ A.comap Y := by rw [← hB₀]; exact w.property
    rcases Submodule.mem_sup.mp hwSum with ⟨b, hb, p, hp, hbp⟩
    have hb₀ : b ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_left hb
    have hp₀ : p ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_right hp
    let bb : B₀ := ⟨b, hb₀⟩
    let pp : B₀ := ⟨p, hp₀⟩
    have heq : w = bb + pp := Subtype.ext hbp.symm
    refine ⟨Y p, hp, ?_⟩
    rw [← hw, heq, map_add, hzero bb hb, hcopy pp hp, zero_add]
  · rintro v ⟨a, ha, hqa⟩
    rcases hAY ha with ⟨p, hp⟩
    have hpA : p ∈ A.comap Y := by change Y p ∈ A; rw [hp]; exact ha
    have hp₀ : p ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_right hpA
    let pp : B₀ := ⟨p, hp₀⟩
    refine ⟨pp, ?_⟩
    rw [hcopy pp hpA, hp, hqa]

omit [FiniteDimensional K W] in
theorem a4_remainder_of_gluing (Y : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B B₀ : Submodule K W)
    (X : B₀ →ₗ[K] (V ⧸ A₀)) (hB₀ : B₀ = B ⊔ A.comap Y)
    (hzero : ∀ b : B₀, (b : W) ∈ B → X b = 0)
    (hcopy : ∀ p : B₀, Y p ∈ A → X p = A₀.mkQ (Y p)) :
    LinearMap.range (compress Y A₀ B₀ - X) ≤ (B.map Y).map A₀.mkQ ∧
      LinearMap.ker X ⊔ LinearMap.ker (compress Y A₀ B₀ - X) = ⊤ := by
  have decomp : ∀ w : B₀, ∃ b p : B₀,
      (b : W) ∈ B ∧ Y p ∈ A ∧ b + p = w := by
    intro w
    have hw : (w : W) ∈ B ⊔ A.comap Y := by rw [← hB₀]; exact w.property
    rcases Submodule.mem_sup.mp hw with ⟨b, hb, p, hp, hbp⟩
    have hb₀ : b ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_left hb
    have hp₀ : p ∈ B₀ := by rw [hB₀]; exact Submodule.mem_sup_right hp
    exact ⟨⟨b, hb₀⟩, ⟨p, hp₀⟩, hb, hp, Subtype.ext hbp⟩
  constructor
  · rintro v ⟨w, hw⟩
    rcases decomp w with ⟨b, p, hb, hp, hbp⟩
    have hz : (compress Y A₀ B₀ - X) w = A₀.mkQ (Y b) := by
      rw [← hbp, map_add]
      change (compress Y A₀ B₀ b - X b) + (compress Y A₀ B₀ p - X p) = A₀.mkQ (Y b)
      rw [hzero b hb, hcopy p hp]
      simp only [compress_apply, sub_zero, sub_self, add_zero]
    exact ⟨Y b, ⟨(b : W), hb, rfl⟩, hz.symm.trans hw⟩
  · apply le_antisymm le_top
    intro w _
    rcases decomp w with ⟨b, p, hb, hp, hbp⟩
    have hpker : p ∈ LinearMap.ker (compress Y A₀ B₀ - X) := by
      change compress Y A₀ B₀ p - X p = 0
      rw [hcopy p hp]
      exact sub_self _
    exact Submodule.mem_sup.mpr ⟨b, hzero b hb, p, hpker, hbp⟩

theorem a4_surviving_index_unique (Y : W →ₗ[K] V)
    (A : Submodule K V) (B : Submodule K W)
    (p q : A4Index (K := K) (W := W) (V := V))
    (hp : A4Survives Y A B p) (hq : A4Survives Y A B q) : p = q := by
  rcases p with ⟨A₀, B₀, X₀⟩
  rcases q with ⟨A₁, B₁, X₁⟩
  rcases hp with ⟨ha₀, hb₀, hi₀, hk₀, him₀, hr₀⟩
  rcases hq with ⟨ha₁, hb₁, hi₁, hk₁, him₁, hr₁⟩
  have heA : A₀ = A₁ := (a4_codomain_forced Y A₀ A B B₀ X₀ ha₀ hb₀ hi₀ hk₀ him₀ hr₀).trans
    (a4_codomain_forced Y A₁ A B B₁ X₁ ha₁ hb₁ hi₁ hk₁ him₁ hr₁).symm
  have heB : B₀ = B₁ := (a4_domain_forced Y A₀ A B B₀ X₀ ha₀ hb₀ hi₀ hk₀ him₀ hr₀).trans
    (a4_domain_forced Y A₁ A B B₁ X₁ ha₁ hb₁ hi₁ hk₁ him₁ hr₁).symm
  subst A₁
  subst B₁
  have heX := a4_map_unique Y A₀ A B B₀ X₀ X₁ ha₀ hb₀ hi₀ hk₀ hk₁ him₀ him₁ hr₀ hr₁
  cases heX
  rfl

end UniqueGamesTheorem.Appendix.LinearIdentities

namespace UniqueGamesTheorem.Appendix.BinaryA4

open LinearIdentities

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 W]

omit [FiniteDimensional F2 W] in
/-- Construct the actual linear map in the canonical (A.4) summand by
gluing zero on `B` with `Q_A₀ Y` on `Y⁻¹(A)`. -/
theorem canonical_glued_map (Y : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W) :
    ∃ X : ↥(B ⊔ A.comap Y) →ₗ[F2] (V ⧸ ((B.map Y) ⊓ A)),
      (∀ b : ↥(B ⊔ A.comap Y), (b : W) ∈ B → X b = 0) ∧
      (∀ p : ↥(B ⊔ A.comap Y), Y p ∈ A → X p = ((B.map Y) ⊓ A).mkQ (Y p)) := by
  let P := A.comap Y
  let A₀ := (B.map Y) ⊓ A
  let B₀ := B ⊔ P
  let pp := P.comap B₀.subtype
  let bb := B.comap B₀.subtype
  let f := compress Y A₀ B₀
  have hc : pp ⊔ bb = ⊤ := by
    apply le_antisymm le_top
    intro w _
    rcases Submodule.mem_sup.mp w.property with ⟨b, hb, p, hp, hbp⟩
    let pv : B₀ := ⟨p, Submodule.mem_sup_right hp⟩
    let bv : B₀ := ⟨b, Submodule.mem_sup_left hb⟩
    refine Submodule.mem_sup.mpr ⟨pv, hp, bv, hb, ?_⟩
    apply Subtype.ext
    change p + b = (w : W)
    rw [add_comm]
    exact hbp
  have compat : ∀ w ∈ pp, w ∈ bb → f w = 0 := by
    intro w hp hb
    have hm : Y w ∈ A₀ := ⟨⟨(w : W), hb, rfl⟩, hp⟩
    change Y w ∈ LinearMap.ker A₀.mkQ
    rw [Submodule.ker_mkQ]
    exact hm
  obtain ⟨X, hcopy, hzero⟩ := DegreeCover.exists_glue_zero pp bb f hc compat
  refine ⟨X, ?_, ?_⟩
  · intro b hb
    exact hzero b hb
  · intro p hp
    exact hcopy p hp

theorem a4_selector_exists (Y : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W)
    (hAY : A ≤ LinearMap.range Y) (hKY : LinearMap.ker Y ≤ B) :
    ∃ p : A4Index (K := F2) (W := W) (V := V), A4Survives Y A B p := by
  obtain ⟨X, hzero, hcopy⟩ := canonical_glued_map Y A B
  let A₀ := (B.map Y) ⊓ A
  let B₀ := B ⊔ A.comap Y
  have inner : Hybrid Y A₀ B₀ := by
    constructor
    · intro a ha
      rcases ha.1 with ⟨b, _, hb⟩
      exact ⟨b, hb⟩
    · intro w hw
      have hy : Y w ∈ (B.map Y) ⊓ A := hw
      exact Submodule.mem_sup_right hy.2
  have hk := a4_kernel_of_gluing Y A₀ A B B₀ X rfl rfl hKY hzero hcopy
  have hi := a4_range_of_gluing Y A₀ A B B₀ X rfl hAY hzero hcopy
  have hr := a4_remainder_of_gluing Y A₀ A B B₀ X rfl hzero hcopy
  have hd := disjoint_quotient_images_of_intersection A₀ A (B.map Y) rfl
  have hl : RankAdditivity.RankBelow X (compress Y A₀ B₀) := by
    apply (RankAdditivity.rankBelow_iff X (compress Y A₀ B₀)).mpr
    refine ⟨?_, hr.2⟩
    rw [hi]
    exact hd.mono_right hr.1
  exact ⟨⟨A₀, B₀, X⟩, inf_le_right, le_sup_left, inner, hk, hi, hl⟩

/-- The complete unique-index selector identity in (A.4) for arbitrary
finite-dimensional binary vector spaces. The index records both subspaces
and the genuine linear map with the required kernel and range. -/
theorem a4_unique_selector (Y : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W) :
    (A ≤ LinearMap.range Y ∧ LinearMap.ker Y ≤ B) ↔
      ∃! p : A4Index (K := F2) (W := W) (V := V), A4Survives Y A B p := by
  constructor
  · rintro ⟨ha, hb⟩
    obtain ⟨p, hp⟩ := a4_selector_exists Y A B ha hb
    exact ⟨p, hp, fun q hq => a4_surviving_index_unique Y A B q p hq hp⟩
  · rintro ⟨⟨A₀, B₀, X⟩, hp, _⟩
    rcases hp with ⟨_, _, inner, hk, hi, hr⟩
    exact a4_weak_selector_of_summand Y A₀ A B B₀ X inner hk hi hr

end UniqueGamesTheorem.Appendix.BinaryA4

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_CompressionCountLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.CompressionCount

open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

universe u v w

variable (U : Type u) (K : Type v) (C : Type w)
variable [AddCommGroup U] [Module F2 U]
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup C] [Module F2 C]

variable {U K C}

variable [FiniteDimensional F2 U] [FiniteDimensional F2 K]

theorem natCard_linearMap [FiniteDimensional F2 C] : Nat.card (U →ₗ[F2] C) =
    2 ^ (finrank F2 U * finrank F2 C) := by
  let e : (Fin (finrank F2 U) → C) ≃ (U →ₗ[F2] C) :=
    ((Module.finBasis F2 U).constr F2).toEquiv
  calc
    Nat.card (U →ₗ[F2] C) = Nat.card C ^ finrank F2 U := by
      rw [← Nat.card_congr e, Nat.card_fun, Nat.card_fin]
    _ = (2 ^ finrank F2 C) ^ finrank F2 U := by
      rw [Module.natCard_eq_pow_finrank (K := F2) (V := C)]
      simp [F2, Nat.card_eq_fintype_card]
    _ = 2 ^ (finrank F2 U * finrank F2 C) := by
      rw [← pow_mul, Nat.mul_comm]

theorem card_parameters (Z : K →ₗ[F2] C) : Nat.card (Parameters (U := U) Z) =
    2 ^ (2 * finrank F2 U * finrank F2 Z.range) := by
  rw [Nat.card_prod, natCard_linearMap, natCard_linearMap, ← pow_add]
  congr 1
  ring

theorem fiber_remainder_rank (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    finrank F2 (Y.val - base U K C).range = finrank F2 Z.range := by
  obtain ⟨P, hP⟩ := (toFiber_bijective Z).2 Y
  have hY : lift Z P = Y.val := congrArg Subtype.val hP
  rw [← hY, range_lift_sub_base]
  exact LinearMap.finrank_range_of_inj (graph_injective Z P.1)

theorem fiber_rank (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    finrank F2 Y.val.range = finrank F2 U + finrank F2 Z.range := by
  rw [Y.property.1, fiber_remainder_rank]

/-- Lemma A.2 in arbitrary finite-dimensional block coordinates. -/
theorem card_fiber (Z : K →ₗ[F2] C) : Nat.card (Fiber (U := U) Z) =
    2 ^ (2 * finrank F2 U * finrank F2 Z.range) := by
  rw [← Nat.card_congr (fiberEquiv (U := U) Z)]
  exact card_parameters Z

end UniqueGamesTheorem.Appendix.CompressionCount

end

section

/-! The actual Appendix A.4 index encoding. Its kernel and range recover the
two subspaces, and its quotient relation recovers the linear map. The final
count follows from this injection into a genuine binary linear-map space. -/

noncomputable section

namespace UniqueGamesTheorem.Appendix.A4IndexCount

section Generic

variable {K : Type*} [Field K]

theorem factorViaRange_apply {U L T : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]
    [AddCommGroup T] [Module K T]
    (X : U →ₗ[K] L) (P : U →ₗ[K] T) (hker : X.ker ≤ P.ker) (u : U) :
    factorViaRange X P hker (X.rangeRestrict u) = P u := by
  have hq : X.quotKerEquivRange.symm (X.rangeRestrict u) = X.ker.mkQ u :=
    X.quotKerEquivRange.symm_apply_apply (X.ker.mkQ u)
  dsimp only [factorViaRange, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hq]
  rfl

theorem factorViaRange_injective {U L T : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]
    [AddCommGroup T] [Module K T]
    (X : U →ₗ[K] L) (P : U →ₗ[K] T) (hker : X.ker = P.ker) :
    Function.Injective (factorViaRange X P hker.le) := by
  intro a b hab
  obtain ⟨u, rfl⟩ := X.surjective_rangeRestrict a
  obtain ⟨v, rfl⟩ := X.surjective_rangeRestrict b
  rw [factorViaRange_apply, factorViaRange_apply] at hab
  have hp : u - v ∈ P.ker := by
    change P (u - v) = 0
    rw [map_sub, hab, sub_self]
  have hx : u - v ∈ X.ker := by rwa [hker]
  apply Subtype.ext
  apply sub_eq_zero.mp
  change X u - X v = 0
  simpa only [LinearMap.mem_ker, map_sub] using hx

theorem factorViaRange_range {U L T : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]
    [AddCommGroup T] [Module K T]
    (X : U →ₗ[K] L) (P : U →ₗ[K] T) (hker : X.ker ≤ P.ker) :
    (factorViaRange X P hker).range = P.range := by
  have hc : (factorViaRange X P hker).comp X.rangeRestrict = P := by
    apply LinearMap.ext
    intro u
    exact factorViaRange_apply X P hker u
  calc
    _ = ((factorViaRange X P hker).comp X.rangeRestrict).range :=
      (LinearMap.range_comp_of_range_eq_top _ X.range_rangeRestrict).symm
    _ = _ := congrArg LinearMap.range hc

variable {V W : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem aToRange_surjective (A A0 : Submodule K V) (B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hR : X.range = A.map A0.mkQ) :
    Function.Surjective (aToRange A A0 B0 X hR) := by
  intro c
  have hc : (c : V ⧸ A0) ∈ A.map A0.mkQ := by rw [← hR]; exact c.property
  rcases Submodule.mem_map.mp hc with ⟨a, ha, he⟩
  exact ⟨⟨a, ha⟩, Subtype.ext he⟩

theorem encodeFixed_relation (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) (a : A) (b : B0) :
    encodeFixed A A0 B B0 X hK hR a = B.mkQ (b : W) ↔ A0.mkQ (a : V) = X b := by
  let P := quotientRestriction B B0
  have hXP : X.ker = P.ker := hK.trans (ker_quotientRestriction B B0).symm
  change factorViaRange X P hXP.le (aToRange A A0 B0 X hR a) = P b ↔ _
  rw [← factorViaRange_apply X P hXP.le b,
    (factorViaRange_injective X P hXP).eq_iff]
  constructor
  · exact fun h => congrArg Subtype.val h
  · exact fun h => Subtype.ext h

theorem ker_encodeFixed (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) :
    (encodeFixed A A0 B B0 X hK hR).ker = A0.comap A.subtype := by
  ext a
  have h := encodeFixed_relation A A0 B B0 X hK hR a (0 : B0)
  simpa using h

theorem range_encodeFixed (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) :
    (encodeFixed A A0 B B0 X hK hR).range = (quotientRestriction B B0).range := by
  rw [encodeFixed, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (aToRange_surjective A A0 B0 X hR))]
  exact factorViaRange_range _ _ _

theorem recover_A0 (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) (hA : A0 ≤ A) :
    (encodeFixed A A0 B B0 X hK hR).ker.map A.subtype = A0 := by
  rw [ker_encodeFixed]
  ext a
  constructor
  · intro ha
    rcases Submodule.mem_map.mp ha with ⟨b, hb, rfl⟩
    exact hb
  · intro ha
    exact Submodule.mem_map.mpr ⟨⟨a, hA ha⟩, ha, rfl⟩

theorem recover_B0 (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) (hB : B ≤ B0) :
    (encodeFixed A A0 B B0 X hK hR).range.comap B.mkQ = B0 := by
  rw [range_encodeFixed]
  ext w
  change B.mkQ w ∈ (quotientRestriction B B0).range ↔ w ∈ B0
  constructor
  · rintro ⟨b, hb⟩
    change B.mkQ (b : W) = B.mkQ w at hb
    have hm : w - (b : W) ∈ B := by
      apply (Submodule.Quotient.mk_eq_zero B).mp
      change B.mkQ (w - (b : W)) = 0
      rw [map_sub, hb, sub_self]
    simpa only [sub_add_cancel] using B0.add_mem (hB hm) b.property
  · intro hw
    exact ⟨⟨w, hw⟩, rfl⟩

theorem encodeFixed_injective (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X X' : B0 →ₗ[K] (V ⧸ A0))
    (hK : X.ker = B.comap B0.subtype) (hR : X.range = A.map A0.mkQ)
    (hK' : X'.ker = B.comap B0.subtype) (hR' : X'.range = A.map A0.mkQ)
    (h : encodeFixed A A0 B B0 X hK hR = encodeFixed A A0 B B0 X' hK' hR') : X = X' := by
  apply LinearMap.ext
  intro b
  have hb : X b ∈ A.map A0.mkQ := by rw [← hR]; exact ⟨b, rfl⟩
  rcases Submodule.mem_map.mp hb with ⟨a, ha, he⟩
  have henc : encodeFixed A A0 B B0 X hK hR ⟨a, ha⟩ = B.mkQ (b : W) :=
    (encodeFixed_relation A A0 B B0 X hK hR ⟨a, ha⟩ b).mpr he
  have henc' : encodeFixed A A0 B B0 X' hK' hR' ⟨a, ha⟩ = B.mkQ (b : W) := by
    rw [← h]
    exact henc
  exact he.symm.trans
    ((encodeFixed_relation A A0 B B0 X' hK' hR' ⟨a, ha⟩ b).mp henc')

theorem encode_injective (A : Submodule K V) (B : Submodule K W) :
    Function.Injective (encode A B) := by
  rintro ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩ ⟨⟨A0', B0', X'⟩, hA', hB', hK', hR'⟩ h
  change encodeFixed A A0 B B0 X hK hR = encodeFixed A A0' B B0' X' hK' hR' at h
  have hAeq : A0 = A0' := by
    calc
      A0 = (encodeFixed A A0 B B0 X hK hR).ker.map A.subtype :=
        (recover_A0 A A0 B B0 X hK hR hA).symm
      _ = (encodeFixed A A0' B B0' X' hK' hR').ker.map A.subtype :=
        congrArg (fun T : A →ₗ[K] (W ⧸ B) => T.ker.map A.subtype) h
      _ = A0' := recover_A0 A A0' B B0' X' hK' hR' hA'
  have hBeq : B0 = B0' := by
    calc
      B0 = (encodeFixed A A0 B B0 X hK hR).range.comap B.mkQ :=
        (recover_B0 A A0 B B0 X hK hR hB).symm
      _ = (encodeFixed A A0' B B0' X' hK' hR').range.comap B.mkQ :=
        congrArg (fun T : A →ₗ[K] (W ⧸ B) => T.range.comap B.mkQ) h
      _ = B0' := recover_B0 A A0' B B0' X' hK' hR' hB'
  cases hAeq
  cases hBeq
  have hXeq := encodeFixed_injective A A0 B B0 X X' hK hR hK' hR' h
  cases hXeq
  rfl

end Generic

section Binary

open Integration.BinaryLinear

variable {V W : Type*} [AddCommGroup V] [Module F2 V]
  [AddCommGroup W] [Module F2 W]
  [FiniteDimensional F2 V] [FiniteDimensional F2 W]

theorem card_index_le (A : Submodule F2 V) (B : Submodule F2 W) :
    Nat.card (Index A B) ≤
      2 ^ (Module.finrank F2 A * Module.finrank F2 (W ⧸ B)) := by
  have hc := CompressionCount.natCard_linearMap (U := A) (C := W ⧸ B)
  let : Finite (A →ₗ[F2] (W ⧸ B)) := Nat.finite_of_card_ne_zero (by
    rw [hc]
    exact pow_ne_zero _ (by decide))
  have h := Nat.card_le_card_of_injective (encode A B) (encode_injective A B)
  rwa [hc] at h

end Binary

end UniqueGamesTheorem.Appendix.A4IndexCount

end

end

section

namespace UniqueGamesTheorem.Appendix.CoordinateTransport

noncomputable section

variable {𝕜 E F : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

theorem finrank_comp_equiv {G : Type*} [AddCommGroup G] [Module 𝕜 G]
    (q : F ≃ₗ[𝕜] G) (Y : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (q.toLinearMap.comp Y).range = Module.finrank 𝕜 Y.range := by
  have h := finrank_range_transport (LinearEquiv.refl 𝕜 E) q Y
  exact h

end

end UniqueGamesTheorem.Appendix.CoordinateTransport

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixCharactersLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Trace characters on actual finite binary matrix spaces. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixCharacters

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear

section LinearMaps

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem linearTracePair_add_right (X : E →ₗ[F2] F) (S T : F →ₗ[F2] E) :
    linearTracePair X (S + T) = linearTracePair X S + linearTracePair X T := by
  simp [linearTracePair, LinearMap.comp_add]

theorem linearTraceCharacter_add (S T : F →ₗ[F2] E) :
    linearTraceCharacter (S + T) = linearTraceCharacter S + linearTraceCharacter T := by
  ext X
  simp only [linearTraceCharacter_apply, linearTracePair_add_right, binarySign_add,
    AddChar.add_apply]

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixCharacters

end

end

section

/-!
# Normalized Fourier analysis of finite binary linear-map spaces

The coefficient normalization is uniform expectation on the primal space. The
Parseval sum over frequencies is an unnormalized sum. The underlying complex
Fourier system is the actual trace-character family on the finite additive group.
Completeness is proved directly from character cancellation and finite sums.
-/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open UniqueGamesTheorem.Fourier.MatrixCharacters

section LinearMaps

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [Fintype (F →ₗ[F2] E)] in
theorem linear_complexCoeff_character (S T : F →ₗ[F2] E) :
    fourierCoeff (linearTraceCharacter S : (E →ₗ[F2] F) → ℂ)
      (linearTraceCharacter T) = if T = S then 1 else 0 := by
  classical
  simp only [fourierCoeff, linearTraceCharacter_star, ← AddChar.add_apply,
    ← linearTraceCharacter_add, Fintype.expect_eq_sum_div_card,
    sum_linearTraceCharacter, linearMap_add_eq_zero_iff]
  by_cases h : S = T
  · subst T
    simp
  · simp [h, Ne.symm h]

theorem linear_fourier_inversion (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re = f X := by
  apply Complex.ofReal_injective
  calc
    ((∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) =
        ∑ S : F →ₗ[F2] E,
          fourierCoeff (fun Y => (f Y : ℂ)) (linearTraceCharacter S) *
            linearTraceCharacter S X := by
      change Complex.ofRealHom (∑ S : F →ₗ[F2] E,
        linearCoeff f S * (linearTraceCharacter S X).re) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      change ((linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) = _
      rw [Complex.ofReal_mul, linearCoeff_complex, linearTraceCharacter_real]
    _ = (f X : ℂ) := linear_complex_inversion _ X

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_sum {J : Type*} (s : Finset J)
    (f : J → (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (∑ j ∈ s, f j) S = ∑ j ∈ s, linearCoeff (f j) S := by
  simp only [linearCoeff, Finset.sum_apply, Finset.sum_mul]
  exact Finset.expect_sum_comm _ _ _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_smul (c : ℝ) (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (c • f) S = c * linearCoeff f S := by
  simp only [linearCoeff, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact Finset.mul_expect _ _ _ |>.symm

omit [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_character (S T : F →ₗ[F2] E) :
    linearCoeff (fun X => (linearTraceCharacter S X).re) T =
      if T = S then 1 else 0 := by
  classical
  apply Complex.ofReal_injective
  rw [linearCoeff_complex]
  simp only [linearTraceCharacter_real, linear_complexCoeff_character]
  split_ifs <;> simp

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixFourier

end

end

section

/-! The degree-zero base case in the actual finite binary Fourier model. -/
noncomputable section
namespace UniqueGamesTheorem.Appendix.DegreeZero
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
theorem rank_pos_of_ne_zero (Y : F →ₗ[F2] E) (hY : Y ≠ 0) :
    0 < Module.finrank F2 Y.range := by
  apply Nat.pos_of_ne_zero
  intro hr
  have hb : Y.range = ⊥ := Submodule.finrank_eq_zero.mp hr
  apply hY
  ext x
  have hx : Y x ∈ Y.range := ⟨x, rfl⟩
  rw [hb] at hx
  exact hx

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem eq_constant_of_degree_zero (f : (E →ₗ[F2] F) → ℝ)
    (hdegree : ∀ Y : F →ₗ[F2] E, 0 < Module.finrank F2 Y.range → linearCoeff f Y = 0)
    (M : E →ₗ[F2] F) : f M = linearCoeff f 0 := by
  classical
  rw [← linear_fourier_inversion f M, Finset.sum_eq_single (0 : F →ₗ[F2] E)]
  · simp
  · intro Y _ hY
    rw [hdegree Y (rank_pos_of_ne_zero Y hY), zero_mul]
  · simp

theorem fourth_moment_eq_energy_sq (f : (E →ₗ[F2] F) → ℝ)
    (hdegree : ∀ Y : F →ₗ[F2] E, 0 < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (𝔼 M, f M^4) = (𝔼 M, f M^2)^2 := by
  simp only [eq_constant_of_degree_zero f hdegree, Fintype.expect_const]
  rw [← pow_mul]

end UniqueGamesTheorem.Appendix.DegreeZero

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_SubspaceCountingLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite-field subspace cardinality bounds used in Appendix A.4. The objects
counted here are actual mathlib submodules, not encoded cardinality assumptions.
-/

namespace UniqueGamesTheorem.Appendix.SubspaceCounting

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V]

theorem span_generators (S : Submodule K V) (k : ℕ) (h : finrank K S = k) :
    Submodule.span K (Set.range (generators S k h)) = S := by
  let b := Module.finBasisOfFinrankEq K S h
  change Submodule.span K (Set.range (S.subtype ∘ b)) = S
  rw [Set.range_comp, Submodule.span_image, b.span_eq]
  simp

/-- A k-subspace is determined by a chosen ordered k-tuple of spanning vectors. -/
theorem card_subspaces_rank_le [Finite V] (k : ℕ) :
    Nat.card {S : Submodule K V // finrank K S = k} ≤ Nat.card V ^ k := by
  classical
  let code : {S : Submodule K V // finrank K S = k} → (Fin k → V) :=
    fun S => generators S.1 k S.2
  have hinj : Function.Injective code := by
    intro S T h
    apply Subtype.ext
    calc
      S.1 = Submodule.span K (Set.range (code S)) := (span_generators S.1 k S.2).symm
      _ = Submodule.span K (Set.range (code T)) :=
        congrArg (fun f : Fin k → V => Submodule.span K (Set.range f)) h
      _ = T.1 := span_generators T.1 k T.2
  simpa only [Nat.card_fun, Nat.card_fin] using Nat.card_le_card_of_injective code hinj

/-- General finite-field form of the image-choice estimate in A.4. -/
theorem card_subspaces_rank_le_field_power [Finite K] (k : ℕ) :
    Nat.card {S : Submodule K V // finrank K S = k} ≤
      Nat.card K ^ (finrank K V * k) := by
  let : Finite V := Finite.of_injective (Module.finBasis K V).equivFun
    (Module.finBasis K V).equivFun.injective
  have h := card_subspaces_rank_le (K := K) (V := V) k
  rwa [Module.natCard_eq_pow_finrank (K := K) (V := V), ← pow_mul] at h

/-- Binary specialization: the ambient dimension is the dimension of Y's image,
not the potentially much larger original vector space. -/
theorem card_binary_subspaces_rank_le
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (d k : ℕ) (hd : finrank (ZMod 2) V ≤ d) :
    Nat.card {S : Submodule (ZMod 2) V // finrank (ZMod 2) S = k} ≤
      2 ^ (d * k) := by
  calc
    _ ≤ Nat.card (ZMod 2) ^ (finrank (ZMod 2) V * k) :=
      card_subspaces_rank_le_field_power (K := ZMod 2) (V := V) k
    _ = 2 ^ (finrank (ZMod 2) V * k) := by simp
    _ ≤ 2 ^ (d * k) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right k hd)

variable {U : Type*} [AddCommGroup U] [Module K U] [Module.Finite K U]

omit [Module.Finite K V] in
/-- Evaluating on a basis bounds the number of linear maps without counting
arbitrary functions on every vector. -/
theorem card_linearMaps_le [Finite V] :
    Nat.card (U →ₗ[K] V) ≤ Nat.card V ^ finrank K U := by
  let b := Module.finBasis K U
  let code : (U →ₗ[K] V) → (Fin (finrank K U) → V) := fun f i => f (b i)
  have hi : Function.Injective code := by
    intro f g h
    apply b.ext
    exact congrFun h
  simpa only [Nat.card_fun, Nat.card_fin] using Nat.card_le_card_of_injective code hi

omit [Module.Finite K V] in
/-- Every rank-k map factors through the actual coordinate vector space K^k. -/
theorem exists_rank_factorization (f : U →ₗ[K] V) (k : ℕ)
    (hk : finrank K (LinearMap.range f) = k) :
    ∃ (a : (Fin k → K) →ₗ[K] V) (b : U →ₗ[K] (Fin k → K)), a.comp b = f := by
  let e := (Module.finBasisOfFinrankEq K (LinearMap.range f) hk).equivFun
  refine ⟨(LinearMap.range f).subtype.comp e.symm.toLinearMap,
    e.toLinearMap.comp f.rangeRestrict, ?_⟩
  ext x
  simp

/-- Rank-k maps between r- and s-dimensional spaces number at most |K|^((r+s)k).
This is a general finite-field bound, proved by selecting the preceding
factorization and injecting into the pair of factor maps. -/
theorem card_rank_maps_le [Finite K] (k : ℕ) :
    Nat.card {f : U →ₗ[K] V // finrank K (LinearMap.range f) = k} ≤
      Nat.card K ^ ((finrank K U + finrank K V) * k) := by
  classical
  let : Finite U := Finite.of_injective (Module.finBasis K U).equivFun
    (Module.finBasis K U).equivFun.injective
  let : Finite V := Finite.of_injective (Module.finBasis K V).equivFun
    (Module.finBasis K V).equivFun.injective
  let A := (Fin k → K) →ₗ[K] V
  let B := U →ₗ[K] (Fin k → K)
  let : Finite A := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let : Finite B := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  have hf (f : {f : U →ₗ[K] V // finrank K (LinearMap.range f) = k}) :
      ∃ p : A × B, p.1.comp p.2 = f.1 := by
    obtain ⟨a, b, h⟩ := exists_rank_factorization f.1 k f.2
    exact ⟨(a, b), h⟩
  let code := fun f => Classical.choose (hf f)
  have hi : Function.Injective code := by
    intro f g h
    apply Subtype.ext
    calc
      f.1 = (code f).1.comp (code f).2 := (Classical.choose_spec (hf f)).symm
      _ = (code g).1.comp (code g).2 := congrArg (fun p : A × B => p.1.comp p.2) h
      _ = g.1 := Classical.choose_spec (hf g)
  calc
    _ ≤ Nat.card (A × B) := Nat.card_le_card_of_injective code hi
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _
    _ ≤ Nat.card V ^ k * (Nat.card K ^ k) ^ finrank K U := by
      apply Nat.mul_le_mul
      · simpa [A] using card_linearMaps_le (K := K) (U := Fin k → K) (V := V)
      · simpa [B, Nat.card_fun] using
          card_linearMaps_le (K := K) (U := U) (V := Fin k → K)
    _ = Nat.card K ^ ((finrank K U + finrank K V) * k) := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := V)]
      simp only [← pow_mul, ← pow_add]
      congr 1
      simp [Nat.mul_add, Nat.mul_comm, Nat.add_comm]

omit [Module.Finite K V] [Module.Finite K U] in
theorem rank_quotientImageMap (Y X : U →ₗ[K] V)
    (hker : LinearMap.ker Y ≤ LinearMap.ker X)
    (himage : LinearMap.range X ≤ LinearMap.range Y) :
    finrank K (LinearMap.range (quotientImageMap Y X hker himage)) =
      finrank K (LinearMap.range X) := by
  rw [← Submodule.finrank_map_subtype_eq (LinearMap.range Y), ← LinearMap.range_comp]
  change finrank K (LinearMap.range ((LinearMap.ker Y).liftQ X hker)) = _
  rw [Submodule.range_liftQ]

omit [Module.Finite K V] in
/-- General ambient-independent rank-k bound for maps constrained by the image
and kernel of Y. This counts actual linear maps; neither cardinality nor
rank-additive predecessor estimates are supplied as hypotheses. -/
theorem card_constrained_maps_le [Finite K] (Y : U →ₗ[K] V) (k : ℕ) :
    Nat.card {X : U →ₗ[K] V // finrank K (LinearMap.range X) = k ∧
      LinearMap.ker Y ≤ LinearMap.ker X ∧ LinearMap.range X ≤ LinearMap.range Y} ≤
      Nat.card K ^ (2 * finrank K (LinearMap.range Y) * k) := by
  classical
  let : Finite (LinearMap.range Y) := Finite.of_injective
    (Module.finBasis K (LinearMap.range Y)).equivFun
    (Module.finBasis K (LinearMap.range Y)).equivFun.injective
  let : Finite (U ⧸ LinearMap.ker Y) := Finite.of_injective
    (Module.finBasis K (U ⧸ LinearMap.ker Y)).equivFun
    (Module.finBasis K (U ⧸ LinearMap.ker Y)).equivFun.injective
  let : Finite ((U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let code (X : {X : U →ₗ[K] V // finrank K (LinearMap.range X) = k ∧
      LinearMap.ker Y ≤ LinearMap.ker X ∧ LinearMap.range X ≤ LinearMap.range Y}) :
      {f : (U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y //
        finrank K (LinearMap.range f) = k} :=
    ⟨quotientImageMap Y X.1 X.2.2.1 X.2.2.2,
      (rank_quotientImageMap Y X.1 X.2.2.1 X.2.2.2).trans X.2.1⟩
  have hi : Function.Injective code := by
    intro X Z h
    apply Subtype.ext
    ext u
    have he := congrArg
      (fun f => ((f : (U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y)
        ((LinearMap.ker Y).mkQ u) : V)) (congrArg Subtype.val h)
    exact he
  have hdim : finrank K (U ⧸ LinearMap.ker Y) = finrank K (LinearMap.range Y) := by
    have hq := (LinearMap.ker Y).finrank_quotient_add_finrank
    have hr := Y.finrank_range_add_finrank_ker
    omega
  calc
    _ ≤ Nat.card {f : (U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y //
        finrank K (LinearMap.range f) = k} := Nat.card_le_card_of_injective code hi
    _ ≤ Nat.card K ^ ((finrank K (U ⧸ LinearMap.ker Y) +
        finrank K (LinearMap.range Y)) * k) :=
      card_rank_maps_le (K := K) (U := U ⧸ LinearMap.ker Y) (V := LinearMap.range Y) k
    _ = _ := by rw [hdim, ← two_mul]

section BinaryPredecessors

variable {U V : Type*} [AddCommGroup U] [AddCommGroup V]
  [Module (ZMod 2) U] [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) U] [Module.Finite (ZMod 2) V]

omit [Module.Finite (ZMod 2) U] [Module.Finite (ZMod 2) V] in
theorem binary_add_cancel (X Y : U →ₗ[ZMod 2] V) : X + (Y + X) = Y := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hself (x : V) : x + x = 0 := by
    rw [← two_smul (ZMod 2) x, htwo, zero_smul]
  ext u
  change X u + (Y u + X u) = Y u
  rw [add_comm (Y u) (X u), ← add_assoc, hself, zero_add]

theorem card_binary_predecessors_le (Y : U →ₗ[ZMod 2] V) (d k : ℕ)
    (hd : finrank (ZMod 2) (LinearMap.range Y) ≤ d) :
    Nat.card {X : U →ₗ[ZMod 2] V // finrank (ZMod 2) (LinearMap.range X) = k ∧
      finrank (ZMod 2) (LinearMap.range Y) =
        finrank (ZMod 2) (LinearMap.range X) +
        finrank (ZMod 2) (LinearMap.range (Y + X))} ≤ 2 ^ (3 * d * k) := by
  classical
  let : Finite U := Finite.of_injective (Module.finBasis (ZMod 2) U).equivFun
    (Module.finBasis (ZMod 2) U).equivFun.injective
  let : Finite V := Finite.of_injective (Module.finBasis (ZMod 2) V).equivFun
    (Module.finBasis (ZMod 2) V).equivFun.injective
  let : Finite (U →ₗ[ZMod 2] V) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let code (X : {X : U →ₗ[ZMod 2] V // finrank (ZMod 2) (LinearMap.range X) = k ∧
      finrank (ZMod 2) (LinearMap.range Y) =
        finrank (ZMod 2) (LinearMap.range X) +
        finrank (ZMod 2) (LinearMap.range (Y + X))}) :
      {X : U →ₗ[ZMod 2] V // finrank (ZMod 2) (LinearMap.range X) = k ∧
        LinearMap.ker Y ≤ LinearMap.ker X ∧ LinearMap.range X ≤ LinearMap.range Y} := by
    have hr : finrank (ZMod 2) (LinearMap.range (X.1 + (Y + X.1))) =
        finrank (ZMod 2) (LinearMap.range X.1) +
        finrank (ZMod 2) (LinearMap.range (Y + X.1)) := by
      rw [binary_add_cancel]
      exact X.2.2
    refine ⟨X.1, X.2.1, ?_, ?_⟩
    · simpa only [binary_add_cancel] using
        RankAdditivity.ker_add_le_ker_left X.1 (Y + X.1) hr
    · simpa only [binary_add_cancel] using
        RankAdditivity.range_left_le_range_add X.1 (Y + X.1) hr
  have hi : Function.Injective code := by
    intro X Z h
    apply Subtype.ext
    change (code X).1 = (code Z).1
    exact congrArg Subtype.val h
  calc
    _ ≤ Nat.card {X : U →ₗ[ZMod 2] V // finrank (ZMod 2) (LinearMap.range X) = k ∧
        LinearMap.ker Y ≤ LinearMap.ker X ∧ LinearMap.range X ≤ LinearMap.range Y} :=
      Nat.card_le_card_of_injective code hi
    _ ≤ Nat.card (ZMod 2) ^ (2 * finrank (ZMod 2) (LinearMap.range Y) * k) :=
      card_constrained_maps_le (K := ZMod 2) Y k
    _ = 2 ^ (2 * finrank (ZMod 2) (LinearMap.range Y) * k) := by simp
    _ ≤ 2 ^ (3 * d * k) := by
      apply Nat.pow_le_pow_right (by decide)
      apply Nat.mul_le_mul_right
      omega

end BinaryPredecessors

end UniqueGamesTheorem.Appendix.SubspaceCounting

end

section

/-! Subspace classification by one additional coordinate and the finite-field
subspace Möbius identity. All spaces, quotients and dimensions are genuine. -/
namespace UniqueGamesTheorem.Appendix.SubspaceExtensions
open scoped BigOperators
open LinearMap Submodule
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem finrank_horizontal [FiniteDimensional K V] (B : Submodule K V) :
    Module.finrank K (horizontal B) = Module.finrank K B := (horizontalEquiv B).finrank_eq.symm

theorem finrank_extension [FiniteDimensional K V] (B : Submodule K V) (q : V ⧸ B) :
    Module.finrank K (extension B q) = Module.finrank K B + 1 := by
  obtain ⟨v,hv⟩ := B.mkQ_surjective q
  have h := (extensionEquiv B q v hv).finrank_eq.symm
  simpa only [Module.finrank_prod,Module.finrank_self] using h

theorem card_eq_pow_finrank [Finite K] [Finite V] [FiniteDimensional K V] :
    Nat.card V = Nat.card K ^ Module.finrank K V := by
  classical
  let := Fintype.ofFinite K
  let := Fintype.ofFinite V
  have h := Fintype.card_congr (Module.finBasis K V).equivFun.toEquiv
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.card_eq_fintype_card] using h

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.SubspaceExtensions.subspaceFintype
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.SubspaceExtensions.quotientFintype
theorem quotient_card_mul_pow [Finite K] [Finite V] [FiniteDimensional K V] (B : Submodule K V) :
    (Nat.card (V ⧸ B) : ℤ) * (Nat.card K : ℤ)^Module.finrank K B =
      (Nat.card K : ℤ)^Module.finrank K V := by
  rw [card_eq_pow_finrank (K:=K) (V:=V ⧸ B)]
  simp only [Nat.cast_pow]
  rw [← pow_add, B.finrank_quotient_add_finrank]

theorem weightedTotal_prod [Finite K] [Finite V] [FiniteDimensional K V] (w : Nat → ℤ) :
    weightedTotal (K:=K) (V:=V × K) w =
      ∑ B : Submodule K V, (w (Module.finrank K B) +
        (Nat.card (V ⧸ B) : ℤ) * w (Module.finrank K B + 1)) := by
  classical
  unfold weightedTotal
  calc
    _ = ∑ a : (Submodule K V) ⊕ (Σ B : Submodule K V, V ⧸ B),
        w (Module.finrank K (encode a)) :=
      (Equiv.sum_comp ((splitEquiv (K:=K) (V:=V)).symm) _).symm
    _ = _ := by
      simp only [Fintype.sum_sum_type,Fintype.sum_sigma,encode,Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro B _
        exact congrArg w (finrank_horizontal B)
      · apply Finset.sum_congr rfl
        intro B _
        calc
          _ = ∑ _q : V ⧸ B, w (Module.finrank K B + 1) := by
            apply Finset.sum_congr rfl
            intro q _
            exact congrArg w (finrank_extension B q)
          _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem mobiusTotal_prod [Finite K] [Finite V] [FiniteDimensional K V] :
    mobiusTotal (K:=K) (V:=V × K) =
      (1 - (Nat.card K : ℤ)^Module.finrank K V) * mobiusTotal (K:=K) (V:=V) := by
  classical
  unfold mobiusTotal
  rw [weightedTotal_prod]
  unfold weightedTotal
  calc
    _ = ∑ B : Submodule K V, (1-(Nat.card K:ℤ)^Module.finrank K V) *
        mobiusWeight (Nat.card K) (Module.finrank K B) := by
      apply Finset.sum_congr rfl
      intro B _
      simp only [mobiusWeight]
      have hcard := quotient_card_mul_pow (K:=K) B
      calc
        _ = mobiusWeight (Nat.card K) (Module.finrank K B) -
            ((Nat.card (V ⧸ B):ℤ)*(Nat.card K:ℤ)^Module.finrank K B) *
              mobiusWeight (Nat.card K) (Module.finrank K B) := by ring
        _ = _ := by rw [hcard]; ring
    _ = _ := by rw [Finset.mul_sum]

variable {W : Type*} [AddCommGroup W] [Module K W]

theorem finrank_map_equiv (e : V ≃ₗ[K] W) (B : Submodule K V) :
    Module.finrank K (B.map e.toLinearMap) = Module.finrank K B := (subspaceMapEquiv e B).finrank_eq.symm

theorem weightedTotal_equiv [Finite V] [Finite W] (e : V ≃ₗ[K] W) (w : Nat → ℤ) :
    weightedTotal (K:=K) (V:=V) w = weightedTotal (K:=K) (V:=W) w := by
  classical
  unfold weightedTotal
  calc
    _ = ∑ B : Submodule K V, w (Module.finrank K (B.map e.toLinearMap)) := by
      apply Finset.sum_congr rfl
      intro B _
      rw [finrank_map_equiv]
    _ = _ := by
      change (∑ B : Submodule K V, w (Module.finrank K (subspaceEquiv e B))) = _
      exact Equiv.sum_comp (subspaceEquiv e) (fun B : Submodule K W => w (Module.finrank K B))

theorem mobiusTotal_equiv [Finite K] [Finite V] [Finite W] (e : V ≃ₗ[K] W) :
    mobiusTotal (K:=K) (V:=V) = mobiusTotal (K:=K) (V:=W) :=
  weightedTotal_equiv e _

theorem mobiusTotal_subsingleton [Finite K] [Finite V] [Subsingleton V] :
    mobiusTotal (K:=K) (V:=V) = 1 := by
  classical
  have hB : ∀ B : Submodule K V, B = ⊥ := by
    intro B
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp
  unfold mobiusTotal weightedTotal
  rw [Finset.sum_eq_single ⊥]
  · simp [mobiusWeight]
  · intro B _ hne
    exact (hne (hB B)).elim
  · intro hn
    exact (hn (Finset.mem_univ _)).elim

theorem coordinate_total_succ [Finite K] (n : Nat) :
    mobiusTotal (K:=K) (V:=Fin (n+1) → K) = 0 := by
  induction n with
  | zero =>
    rw [mobiusTotal_equiv (coordinateSplit (K:=K) 0),mobiusTotal_prod]
    simp [Module.finrank_zero_of_subsingleton]
  | succ n ih =>
    rw [mobiusTotal_equiv (coordinateSplit (K:=K) (n+1)),mobiusTotal_prod,ih,mul_zero]

theorem mobiusTotal_eq_if [Finite K] [Finite V] [FiniteDimensional K V] :
    mobiusTotal (K:=K) (V:=V) = if Module.finrank K V = 0 then 1 else 0 := by
  rw [mobiusTotal_equiv (Module.finBasis K V).equivFun]
  cases hd : Module.finrank K V with
  | zero => simpa [hd] using (mobiusTotal_subsingleton (K:=K) (V:=Fin 0 → K))
  | succ n => simpa [hd] using (coordinate_total_succ (K:=K) n)

theorem mobiusWeight_closed (q n : Nat) :
    mobiusWeight q n = (-1:ℤ)^n * (q:ℤ)^(n.choose 2) := by
  induction n with
  | zero => simp [mobiusWeight]
  | succ n ih =>
    rw [mobiusWeight,ih,Nat.choose_succ_succ]
    simp only [Nat.choose_one_right,pow_add,pow_succ]
    ring

theorem binary_subspace_mobius {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [Finite E] [FiniteDimensional (ZMod 2) E] :
    weightedTotal (K:=ZMod 2) (V:=E) (fun d => (-1:ℤ)^d * 2^(d.choose 2)) =
      if Module.finrank (ZMod 2) E = 0 then 1 else 0 := by
  have h := mobiusTotal_eq_if (K:=ZMod 2) (V:=E)
  have hq : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  simpa only [mobiusTotal,weightedTotal,mobiusWeight_closed,hq,Nat.cast_ofNat] using h

end
end UniqueGamesTheorem.Appendix.SubspaceExtensions

end

section

namespace UniqueGamesTheorem.Appendix.SubmoduleInterval
open Module
variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

theorem lowerInterval_finrank (I : Submodule 𝕜 V)
    (A : {A : Submodule 𝕜 V // A ≤ I}) :
    finrank 𝕜 (lowerIntervalEquiv I A) = finrank 𝕜 A.val :=
  (lowerIntervalSpaceEquiv I A).finrank_eq.symm

open scoped BigOperators
attribute [local instance] Classical.propDecidable

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.SubmoduleInterval.submoduleFinite
theorem lowerWeightedTotal_eq [Finite V] (I : Submodule 𝕜 V) (w : Nat → ℤ) :
    lowerWeightedTotal I w = SubspaceExtensions.weightedTotal (K := 𝕜) (V := I) w := by
  classical
  let := Fintype.ofFinite {A : Submodule 𝕜 V // A ≤ I}
  let := SubspaceExtensions.subspaceFintype (K := 𝕜) (V := I)
  unfold lowerWeightedTotal SubspaceExtensions.weightedTotal
  exact Fintype.sum_equiv (lowerIntervalEquiv I)
    (fun A : {A : Submodule 𝕜 V // A ≤ I} => w (finrank 𝕜 A.val))
    (fun B : Submodule 𝕜 I => w (finrank 𝕜 B))
    (fun A => congrArg w (lowerInterval_finrank I A).symm)

theorem binary_lower_interval_mobius {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [Finite E] [FiniteDimensional (ZMod 2) E] (I : Submodule (ZMod 2) E) :
    lowerWeightedTotal I (fun r => (-1 : ℤ)^r * 2^(r.choose 2)) =
      if I = ⊥ then 1 else 0 := by
  rw [lowerWeightedTotal_eq, SubspaceExtensions.binary_subspace_mobius]
  simp only [Submodule.finrank_eq_zero]

end UniqueGamesTheorem.Appendix.SubmoduleInterval

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixRestrictions
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Fourier.MatrixRestrictions

open UniqueGamesTheorem.Integration.BinaryLinear
open scoped BigOperators

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup C] [Module F2 C]

theorem embed_injective (W : Submodule F2 E)
    (C' : Submodule F2 C) : Function.Injective (embed W C') := by
  intro A B h
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := W.mkQ_surjective x
  apply Subtype.ext
  exact congrArg (fun f : (E →ₗ[F2] C) => f y) h

theorem embed_vanishes (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') :
    W ≤ LinearMap.ker (embed W C' A) := by
  intro x hx
  change (A (W.mkQ x) : C) = 0
  have hzero : W.mkQ x = 0 := by simpa using hx
  simp [hzero]

theorem embed_range (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') :
    LinearMap.range (embed W C' A) ≤ C' := by
  rintro x ⟨y, rfl⟩
  exact (A (W.mkQ y)).property

/-- These are exactly the maps vanishing on `W` with image in `C'`. -/
theorem exists_embed_iff (W : Submodule F2 E)
    (C' : Submodule F2 C) (B : (E →ₗ[F2] C)) :
    (∃ A : Parameter W C', embed W C' A = B) ↔
      W ≤ LinearMap.ker B ∧ LinearMap.range B ≤ C' := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨embed_vanishes W C' A, embed_range W C' A⟩
  · rintro ⟨hW, hC⟩
    let B' : E →ₗ[F2] C' :=
      B.codRestrict C' (fun x => hC ⟨x, rfl⟩)
    have hker : W ≤ LinearMap.ker B' := by
      intro x hx
      apply Subtype.ext
      exact hW hx
    refine ⟨W.liftQ B' hker, ?_⟩
    apply LinearMap.ext
    intro x
    rfl

end UniqueGamesTheorem.Fourier.MatrixRestrictions

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_A13IndexLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Finite scalar estimates in the Appendix A.5 induction

The geometric estimate retains the original positive-order condition
`1 ≤ i + j + k`; deleting the origin is essential when `k = 0`.
-/

noncomputable section
open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.A5Scalar

theorem absorption {d : ℕ} (hd : 1 ≤ d) :
    (162 : ℝ) * (((2 : ℝ) ^ (94 * d * d))⁻¹ +
      ((2 : ℝ) ^ (31 * d - 1))⁻¹) ≤ 1 := by
  have hdd : 1 ≤ d * d := hd.trans (Nat.le_mul_self d)
  have he₁ : 9 ≤ 94 * d * d := by nlinarith
  have he₂ : 9 ≤ 31 * d - 1 := by omega
  have hp₁ : (512 : ℝ) ≤ (2 : ℝ) ^ (94 * d * d) := by
    calc
      _ = (2 : ℝ) ^ 9 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he₁
  have hp₂ : (512 : ℝ) ≤ (2 : ℝ) ^ (31 * d - 1) := by
    calc
      _ = (2 : ℝ) ^ 9 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he₂
  have hb₁ : (512 : ℝ) * ((2 : ℝ) ^ (94 * d * d))⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hp₁
      (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (94 * d * d)))
    simpa only [mul_inv_cancel₀ (pow_ne_zero (94 * d * d) (two_ne_zero : (2 : ℝ) ≠ 0))] using h
  have hb₂ : (512 : ℝ) * ((2 : ℝ) ^ (31 * d - 1))⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hp₂
      (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (31 * d - 1)))
    simpa only [mul_inv_cancel₀ (pow_ne_zero (31 * d - 1) (two_ne_zero : (2 : ℝ) ≠ 0))] using h
  linarith

theorem geometric_sum_le (q : ℝ) (n : ℕ) (hq₀ : 0 ≤ q) (hq : q ≤ 1 / 4) :
    (∑ i ∈ Finset.range n, q ^ i) ≤ 4 / 3 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [pow_succ, pow_zero, ← Finset.sum_mul]
    nlinarith [mul_le_mul_of_nonneg_right ih hq₀]

theorem pair_sum_factor (q : ℝ) (n m k : ℕ) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1), q ^ (i + j + k)) =
      ((∑ i ∈ Finset.range (n + 1), q ^ i) *
        (∑ j ∈ Finset.range (m + 1), q ^ j)) * q ^ k := by
  simp only [pow_add, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The exact decomposition with the origin deleted. -/
theorem positiveSum_zero_eq (q : ℝ) (n m : ℕ) :
    positiveSum q n m 0 =
      q * ((∑ i ∈ Finset.range n, q ^ i) * (∑ j ∈ Finset.range (m + 1), q ^ j)) +
        q * (∑ j ∈ Finset.range m, q ^ j) := by
  have htail : (∑ j ∈ Finset.range (m + 1), if 1 ≤ j then q ^ j else 0) =
      q * (∑ j ∈ Finset.range m, q ^ j) := by
    rw [Finset.sum_range_succ']
    simp [pow_succ, Finset.mul_sum, mul_comm]
  have hshift : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (m + 1), q ^ (i + 1 + j)) =
      q * ((∑ i ∈ Finset.range n, q ^ i) * (∑ j ∈ Finset.range (m + 1), q ^ j)) := by
    simp only [pow_add, pow_one, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpos : ∀ i j : ℕ, 1 ≤ i + 1 + j := by
    intro i j
    omega
  unfold positiveSum
  rw [Finset.sum_range_succ']
  simp only [Nat.add_zero, Nat.zero_add, hpos, ↓reduceIte]
  rw [htail, hshift]

theorem positiveSum_zero_le (q : ℝ) (n m : ℕ) (hq₀ : 0 ≤ q) (hq : q ≤ 1 / 4) :
    positiveSum q n m 0 ≤ 4 * q := by
  have hn := geometric_sum_le q n hq₀ hq
  have hm := geometric_sum_le q (m + 1) hq₀ hq
  have hm' := geometric_sum_le q m hq₀ hq
  have hm₀ : 0 ≤ ∑ j ∈ Finset.range (m + 1), q ^ j :=
    Finset.sum_nonneg (fun j _ => pow_nonneg hq₀ j)
  have hp := mul_le_mul hn hm hm₀ (by norm_num : (0 : ℝ) ≤ 4 / 3)
  rw [positiveSum_zero_eq]
  have h₁ := mul_le_mul_of_nonneg_left hp hq₀
  have h₂ := mul_le_mul_of_nonneg_left hm' hq₀
  nlinarith

theorem positiveSum_pos_le (q : ℝ) (n m k : ℕ) (hq₀ : 0 ≤ q)
    (hq : q ≤ 1 / 4) (hk : 1 ≤ k) : positiveSum q n m k ≤ 2 * q ^ k := by
  have hpos : ∀ i j : ℕ, 1 ≤ i + j + k := by
    intro i j
    omega
  simp only [positiveSum, hpos, ↓reduceIte]
  rw [pair_sum_factor]
  have hn := geometric_sum_le q (n + 1) hq₀ hq
  have hm := geometric_sum_le q (m + 1) hq₀ hq
  have hm₀ : 0 ≤ ∑ j ∈ Finset.range (m + 1), q ^ j :=
    Finset.sum_nonneg (fun j _ => pow_nonneg hq₀ j)
  have hp := mul_le_mul hn hm hm₀ (by norm_num : (0 : ℝ) ≤ 4 / 3)
  calc
    _ ≤ ((4 / 3 : ℝ) * (4 / 3)) * q ^ k :=
      mul_le_mul_of_nonneg_right hp (pow_nonneg hq₀ k)
    _ ≤ 2 * q ^ k := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hq₀ k)

/-- The original positive-order geometric bound in (A.16), with independent
finite truncations. No upper bound on `k` is required. -/
theorem a16_finite_geometric (d n m k : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
      if 1 ≤ i + j + k then ((2 : ℝ)⁻¹) ^ (63 * d * (i + j + k)) else 0) ≤
        ((2 : ℝ)⁻¹) ^ (31 * d * (k + 1)) := by
  let q : ℝ := ((2 : ℝ)⁻¹) ^ (63 * d)
  have hq₀ : 0 ≤ q := pow_nonneg (by norm_num) _
  have hq : q ≤ (1 / 4 : ℝ) := by
    calc
      _ ≤ ((2 : ℝ)⁻¹) ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = _ := by norm_num
  have heq : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
      if 1 ≤ i + j + k then ((2 : ℝ)⁻¹) ^ (63 * d * (i + j + k)) else 0) =
        positiveSum q n m k := by
    simp only [positiveSum, q, pow_mul]
  rw [heq]
  by_cases hk : k = 0
  · subst k
    calc
      _ ≤ 4 * q := positiveSum_zero_le q n m hq₀ hq
      _ ≤ 4 * ((2 : ℝ)⁻¹) ^ (31 * d + 2) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) (by norm_num)
      _ = ((2 : ℝ)⁻¹) ^ (31 * d * (0 + 1)) := by
          norm_num [pow_add]
          ring
  · have hkpos : 1 ≤ k := by omega
    have hs := Induction.positive_rank_geometric_slack d k hkpos
    have hex : 31 * d * (k + 1) + 1 ≤ 63 * d * k := by nlinarith
    calc
      _ ≤ 2 * q ^ k := positiveSum_pos_le q n m k hq₀ hq hkpos
      _ = 2 * ((2 : ℝ)⁻¹) ^ (63 * d * k) := by
        dsimp only [q]
        rw [← pow_mul]
      _ ≤ 2 * ((2 : ℝ)⁻¹) ^ (31 * d * (k + 1) + 1) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hex) (by norm_num)
      _ = ((2 : ℝ)⁻¹) ^ (31 * d * (k + 1)) := by
          norm_num [pow_add]
          ring

theorem a16_original_range (d k : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1),
      if 1 ≤ i + j + k then ((2 : ℝ)⁻¹) ^ (63 * d * (i + j + k)) else 0) ≤
        ((2 : ℝ)⁻¹) ^ (31 * d * (k + 1)) :=
  a16_finite_geometric d d d k hd

end UniqueGamesTheorem.Appendix.A5Scalar

end

end

section

noncomputable section
open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.A5WeightedReindex

attribute [local instance] Classical.propDecidable

theorem exponent_weight_le (d t k : ℕ) (ht : t ≤ d) (hk : k ≤ t) :
    (2 : ℝ) ^ (100 * (d - t) ^ 2 + 27 * d * t + 6 * d * k) ≤
      (2 : ℝ) ^ (100 * d * d) * ((2 : ℝ)⁻¹) ^ (63 * d * t + 4 * d * k) := by
  have he : (100 * (d - t) ^ 2 + 27 * d * t + 6 * d * k) +
      (63 * d * t + 4 * d * k) ≤ 100 * d * d := by
    simpa only [pow_two, Nat.mul_assoc, Nat.add_assoc] using
      Induction.induction_exponent_budget d t k ht hk
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he
  rw [pow_add] at hp
  have hn : (2 : ℝ) ^ (63 * d * t + 4 * d * k) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hm := mul_le_mul_of_nonneg_right hp
    (inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (63 * d * t + 4 * d * k)))
  rw [mul_assoc, mul_inv_cancel₀ hn, mul_one] at hm
  simpa only [inv_pow] using hm

theorem counted_weight_le (d t k c : ℕ) (ht : t ≤ d) (hk : k ≤ t)
    (hc : c ≤ 2 ^ (3 * d * t)) :
    (c : ℝ) * (2 : ℝ) ^ (100 * (d - t) ^ 2 + 24 * d * t + 6 * d * k) ≤
      (2 : ℝ) ^ (100 * d * d) * ((2 : ℝ)⁻¹) ^ (63 * d * t + 4 * d * k) := by
  have hc' : (c : ℝ) ≤ (2 : ℝ) ^ (3 * d * t) := by exact_mod_cast hc
  calc
    _ ≤ (2 : ℝ) ^ (3 * d * t) *
        (2 : ℝ) ^ (100 * (d - t) ^ 2 + 24 * d * t + 6 * d * k) :=
      mul_le_mul_of_nonneg_right hc' (pow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (100 * (d - t) ^ 2 + 27 * d * t + 6 * d * k) := by
      rw [← pow_add]
      congr 1
      ring
    _ ≤ _ := exponent_weight_le d t k ht hk

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Exact finite grouping by the actual result and both dimension indices. -/
theorem sum_grouped (d : ℕ) (result : α → β) (i j : α → ℕ)
    (hbound : ∀ a, i a ≤ d ∧ j a ≤ d) (C : β → ℕ → ℕ → ℝ) :
    (∑ a, C (result a) (i a) (j a)) =
      ∑ b, ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1),
        ((fiber result i j b r s).card : ℝ) * C b r s := by
  classical
  let key : α → β × ℕ × ℕ := fun a => (result a, i a, j a)
  let target : Finset (β × ℕ × ℕ) :=
    Finset.univ ×ˢ (Finset.range (d + 1) ×ˢ Finset.range (d + 1))
  let G : β × ℕ × ℕ → ℝ := fun p => C p.1 p.2.1 p.2.2
  have hmap : ∀ a ∈ (Finset.univ : Finset α), key a ∈ target := by
    intro a _
    simp only [target, key, Finset.mem_product, Finset.mem_univ,
      Finset.mem_range, true_and]
    exact ⟨Nat.lt_succ_iff.mpr (hbound a).1, Nat.lt_succ_iff.mpr (hbound a).2⟩
  have h := Finset.sum_fiberwise_of_maps_to' (s := Finset.univ) (t := target)
    (g := key) hmap G
  simpa only [target, Finset.sum_product, G, key, Prod.mk.injEq,
    Finset.sum_const, nsmul_eq_mul, fiber] using h.symm

theorem weighted_reindex (d : ℕ) (hd : 1 ≤ d)
    (result : α → β) (i j : α → ℕ) (k : β → ℕ) (w : β → ℝ)
    (hw : ∀ b, 0 ≤ w b)
    (horder : ∀ a, 1 ≤ i a + j a + k (result a) ∧ i a + j a + k (result a) ≤ d)
    (hcard : ∀ b r s,
      Nat.card {a : α // result a = b ∧ i a = r ∧ j a = s} ≤
        2 ^ (3 * d * (r + s + k b))) :
    (∑ a, (2 : ℝ) ^ (100 * (d - (i a + j a + k (result a))) ^ 2 +
        24 * d * (i a + j a + k (result a)) + 6 * d * k (result a)) * w (result a)) ≤
      (2 : ℝ) ^ (100 * d * d) *
        ∑ b, ((2 : ℝ)⁻¹) ^ (31 * d * (k b + 1) + 4 * d * k b) * w b := by
  classical
  let C : β → ℕ → ℕ → ℝ := fun b r s =>
    (2 : ℝ) ^ (100 * (d - (r + s + k b)) ^ 2 +
      24 * d * (r + s + k b) + 6 * d * k b) * w b
  let envelope : β → ℝ := fun b =>
    (2 : ℝ) ^ (100 * d * d) * ((2 : ℝ)⁻¹) ^ (4 * d * k b) * w b
  have henvelope : ∀ b, 0 ≤ envelope b := by
    intro b
    exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
      (pow_nonneg (by norm_num) _)) (hw b)
  have hbound : ∀ a, i a ≤ d ∧ j a ≤ d := by
    intro a
    have h := (horder a).2
    omega
  have hfiber : ∀ b r s,
      ((fiber result i j b r s).card : ℝ) * C b r s ≤
        envelope b * (if 1 ≤ r + s + k b then
          ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b)) else 0) := by
    intro b r s
    by_cases hne : (fiber result i j b r s).Nonempty
    · obtain ⟨a, ha⟩ := hne
      rcases Finset.mem_filter.mp ha with ⟨_, hr, hi, hj⟩
      have ht := horder a
      rw [hr, hi, hj] at ht
      have hc : (fiber result i j b r s).card ≤ 2 ^ (3 * d * (r + s + k b)) := by
        simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, fiber] using hcard b r s
      have hweight := counted_weight_le d (r + s + k b) (k b)
        (fiber result i j b r s).card ht.2 (by omega) hc
      rw [ite_eq_left ht.1]
      calc
        _ = (((fiber result i j b r s).card : ℝ) *
            (2 : ℝ) ^ (100 * (d - (r + s + k b)) ^ 2 +
              24 * d * (r + s + k b) + 6 * d * k b)) * w b := by
          dsimp only [C]
          ring
        _ ≤ ((2 : ℝ) ^ (100 * d * d) *
            ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b) + 4 * d * k b)) * w b :=
          mul_le_mul_of_nonneg_right hweight (hw b)
        _ = envelope b * ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b)) := by
          dsimp only [envelope]
          rw [pow_add]
          ring
    · have hz : (fiber result i j b r s).card = 0 := by
        exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
      rw [hz, Nat.cast_zero, zero_mul]
      apply mul_nonneg (henvelope b)
      split_ifs <;> positivity
  change (∑ a, C (result a) (i a) (j a)) ≤ _
  rw [sum_grouped d result i j hbound C]
  calc
    _ ≤ ∑ b, ∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1),
        envelope b * (if 1 ≤ r + s + k b then
          ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b)) else 0) := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro r _
      exact Finset.sum_le_sum (fun s _ => hfiber b r s)
    _ = ∑ b, envelope b *
        (∑ r ∈ Finset.range (d + 1), ∑ s ∈ Finset.range (d + 1),
          if 1 ≤ r + s + k b then ((2 : ℝ)⁻¹) ^ (63 * d * (r + s + k b)) else 0) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ b, envelope b * ((2 : ℝ)⁻¹) ^ (31 * d * (k b + 1)) := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (A5Scalar.a16_original_range d (k b) hd) (henvelope b)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [envelope]
      rw [pow_add]
      ring

end UniqueGamesTheorem.Appendix.A5WeightedReindex

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_DerivativeInduction
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.DerivativeInduction

open UniqueGamesTheorem.Integration.BinaryLinear
open LinearMap

variable {B U A C : Type*}
variable [AddCommGroup B] [Module F2 B] [AddCommGroup U] [Module F2 U]
variable [AddCommGroup A] [Module F2 A] [AddCommGroup C] [Module F2 C]

section Subspaces

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

/-- Exact antecedent cardinality in arbitrary complementary subspaces. -/
theorem card_subspaceAntecedent (P E : Submodule F2 W)
    (Q D : Submodule F2 V) (hP : IsCompl P E) (hQ : IsCompl Q D)
    (Z : P →ₗ[F2] D) [Module.Finite F2 W] [Module.Finite F2 V] :
    Nat.card (SubspaceAntecedent P Q D hQ Z) =
      2 ^ (Module.finrank F2 Z.range *
        (Module.finrank F2 Q + Module.finrank F2 E)) := by
  rw [Nat.card_congr (subspaceAntecedentEquiv P E Q D hP hQ Z), Nat.card_prod,
    CompressionCount.natCard_linearMap, CompressionCount.natCard_linearMap, ← pow_add]
  congr 1
  ring

end Subspaces

end UniqueGamesTheorem.Appendix.DerivativeInduction

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_AntecedentCountLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact antecedents of quotient compression

This is the reverse-map count used in Proposition A.5. The compressed map is
fixed, together with the two removed subspaces; neither a prescribed rank nor
an assumed cardinality is part of the antecedent predicate.
-/

namespace UniqueGamesTheorem.Appendix.AntecedentCount

open UniqueGamesTheorem.Integration.BinaryLinear
open LinearIdentities
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

variable [FiniteDimensional F2 W] [FiniteDimensional F2 V]

/-- Exact number of antecedents of a fixed quotient compression. The graph
and omitted-domain parameters have `rank Y * (dim Q + codim P)` bits. -/
theorem card_antecedent (P : Submodule F2 W) (Q : Submodule F2 V)
    (Y : P →ₗ[F2] (V ⧸ Q)) :
    Nat.card (Antecedent P Q Y) =
      2 ^ (Module.finrank F2 Y.range *
        (Module.finrank F2 Q + Module.finrank F2 (W ⧸ P))) := by
  obtain ⟨E, hP⟩ := P.exists_isCompl
  obtain ⟨D, hQ⟩ := Q.exists_isCompl
  rw [Nat.card_congr (subspaceEquiv P Q D hQ Y),
    DerivativeInduction.card_subspaceAntecedent P E Q D hP hQ]
  rw [CoordinateTransport.finrank_comp_equiv]
  rw [← (P.quotientEquivOfIsCompl E hP).finrank_eq]

/-- The actual reverse-map multiplicity fits the two graph-parameter budgets
used in (A.16). No additional isomorphism factor is needed. -/
theorem card_antecedent_le (P : Submodule F2 W) (Q : Submodule F2 V)
    (Y : P →ₗ[F2] (V ⧸ Q)) (d k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hQ : Module.finrank F2 Q ≤ d)
    (hP : Module.finrank F2 (W ⧸ P) ≤ d) :
    Nat.card (Antecedent P Q Y) ≤ 2 ^ (2 * d * k) := by
  rw [card_antecedent]
  apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
  calc
    Module.finrank F2 Y.range *
        (Module.finrank F2 Q + Module.finrank F2 (W ⧸ P)) ≤ k * (d + d) :=
      Nat.mul_le_mul hY (Nat.add_le_add hQ hP)
    _ = 2 * d * k := by ring

end

end UniqueGamesTheorem.Appendix.AntecedentCount

end

section

/-!
# Exact compression fibers for arbitrary binary linear maps

This is the general cardinality assertion in Lemma A.2, with the actual kernel
restriction and range quotient. The map X is arbitrary; no chosen-coordinate
or fixed-dimension hypothesis occurs in `card_fiber`.
-/

namespace UniqueGamesTheorem.Appendix.FullCompression

open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.CoordinateTransport
open Module

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 F] in
/-- Lemma A.2: every compressed rank-r map has exactly `2^(2*k*r)`
rank-additive lifts above an arbitrary rank-k map X. -/
theorem card_fiber (X : E →ₗ[F2] F) (Z : X.ker →ₗ[F2] (F ⧸ X.range)) :
    Nat.card (Fiber X Z) = 2 ^ (2 * finrank F2 X.range * finrank F2 Z.range) := by
  obtain ⟨P, hP⟩ := X.ker.exists_isCompl
  obtain ⟨C, hC⟩ := X.range.exists_isCompl
  rw [Nat.card_congr (fiberEquiv X Z P hP C hC), CompressionCount.card_fiber,
    finrank_comp_equiv]

omit [FiniteDimensional F2 F] in
/-- Every member of a compression fiber has rank `rank X + rank Z`. -/
theorem fiber_rank (X : E →ₗ[F2] F)
    (Z : X.ker →ₗ[F2] (F ⧸ X.range)) (Y : Fiber X Z) :
    finrank F2 Y.val.range = finrank F2 X.range + finrank F2 Z.range := by
  obtain ⟨P, hP⟩ := X.ker.exists_isCompl
  obtain ⟨C, hC⟩ := X.range.exists_isCompl
  have h := CompressionCount.fiber_rank
    ((X.range.quotientEquivOfIsCompl C hC).toLinearMap.comp Z)
    ((fiberEquiv X Z P hP C hC) Y)
  change finrank F2 (toBlocks X P hP C hC Y.val).range =
    finrank F2 X.range +
      finrank F2 ((X.range.quotientEquivOfIsCompl C hC).toLinearMap.comp Z).range at h
  rw [finrank_toBlocks, finrank_comp_equiv] at h
  exact h

end

end UniqueGamesTheorem.Appendix.FullCompression

end

section

/-! Exact coefficient-energy estimate underlying (A.10), with genuine
binary linear maps, their rank-additive order and quotient compression. -/
namespace UniqueGamesTheorem.Appendix.DerivativeEnergy

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankAdditivity (RankBelow)

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)]

omit [FiniteDimensional F2 F] in
theorem supported_fiber_energy (X : E →ₗ[F2] F)
    [Fintype (X.ker →ₗ[F2] (F ⧸ X.range))]
    (s : Finset (E →ₗ[F2] F)) (a : (E →ₗ[F2] F) → ℝ) (d : Nat)
    (hs : ∀ Y ∈ s, RankBelow X Y ∧ finrank F2 Y.range ≤ d) :
    (∑ Z, (∑ Y ∈ s.filter (fun Y => FullCompression.compression X Y = Z), a Y)^2) ≤
      (2 : ℝ)^(2 * finrank F2 X.range * (d - finrank F2 X.range)) *
        ∑ Y ∈ s, a Y^2 := by
  classical
  apply FiberEnergy.finite_fiber_energy
  intro Z
  let t := s.filter (fun Y => FullCompression.compression X Y = Z)
  by_cases ht : t.Nonempty
  · obtain ⟨Y, hY⟩ := ht
    have hy := Finset.mem_filter.mp hY
    have hys := hs Y hy.1
    let yz : FullCompression.Fiber X Z := ⟨Y, hys.1, hy.2⟩
    have hr := FullCompression.fiber_rank X Z yz
    have hz : finrank F2 Z.range ≤ d - finrank F2 X.range := by
      change finrank F2 Y.range = finrank F2 X.range + finrank F2 Z.range at hr
      omega
    let emb : ↥t → FullCompression.Fiber X Z := fun y =>
      ⟨y.val, (hs y.val (Finset.mem_filter.mp y.property).1).1,
        (Finset.mem_filter.mp y.property).2⟩
    have hemb : Function.Injective emb := by
      intro y y' h
      have hv : y.val = y'.val :=
        congrArg (fun z : FullCompression.Fiber X Z => z.val) h
      exact Subtype.ext hv
    let : Finite (FullCompression.Fiber X Z) :=
      Finite.of_injective (fun z : FullCompression.Fiber X Z => z.val)
        (fun _ _ h => Subtype.ext h)
    have hc : t.card ≤ Nat.card (FullCompression.Fiber X Z) := by
      have h := Nat.card_le_card_of_injective emb hemb
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h
    rw [FullCompression.card_fiber X Z] at hc
    have hpow := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2)
      (Nat.mul_le_mul_left (2 * finrank F2 X.range) hz)
    have hnat : t.card ≤ 2^(2 * finrank F2 X.range * (d - finrank F2 X.range)) :=
      hc.trans hpow
    exact_mod_cast hnat
  · have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change (t.card : ℝ) ≤ _
    rw [he, Finset.card_empty, Nat.cast_zero]
    positivity

omit [FiniteDimensional F2 F] in
/-- The precise merged-coefficient form of (A.10). Coefficients are arbitrary
real numbers with the stated degree support, not assumed nonnegative. -/
theorem coefficient_energy (X : E →ₗ[F2] F)
    [Fintype (X.ker →ₗ[F2] (F ⧸ X.range))]
    (a : (E →ₗ[F2] F) → ℝ) (d : Nat)
    (hdegree : ∀ Y, d < finrank F2 Y.range → a Y = 0) :
    (∑ Z, (∑ Y, if RankBelow X Y ∧ FullCompression.compression X Y = Z
      then a Y else 0)^2) ≤
      (2 : ℝ)^(2 * finrank F2 X.range * (d - finrank F2 X.range)) *
        ∑ Y, if RankBelow X Y then a Y^2 else 0 := by
  classical
  let s := Finset.univ.filter (fun Y : E →ₗ[F2] F =>
    RankBelow X Y ∧ finrank F2 Y.range ≤ d)
  have hs : ∀ Y ∈ s, RankBelow X Y ∧ finrank F2 Y.range ≤ d := by
    intro Y hY
    exact (Finset.mem_filter.mp hY).2
  have hsum (Z : X.ker →ₗ[F2] (F ⧸ X.range)) :
      (∑ Y ∈ s.filter (fun Y => FullCompression.compression X Y = Z), a Y) =
        ∑ Y, if RankBelow X Y ∧ FullCompression.compression X Y = Z then a Y else 0 := by
    simp only [s, Finset.filter_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro Y _
    by_cases hy : finrank F2 Y.range ≤ d
    · by_cases ho : RankBelow X Y <;> simp [hy, ho]
    · have ha : a Y = 0 := hdegree Y (Nat.lt_of_not_ge hy)
      simp [ha]
  have henergy : (∑ Y ∈ s, a Y^2) =
      ∑ Y, if RankBelow X Y then a Y^2 else 0 := by
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro Y _
    by_cases hy : finrank F2 Y.range ≤ d
    · by_cases ho : RankBelow X Y <;> simp [hy, ho]
    · have ha : a Y = 0 := hdegree Y (Nat.lt_of_not_ge hy)
      simp [ha]
  simpa only [hsum, henergy] using supported_fiber_energy X s a d hs

end UniqueGamesTheorem.Appendix.DerivativeEnergy

end

section

namespace UniqueGamesTheorem.Appendix.TotalPredecessorCount
open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankAdditivity
variable {E F : Type*} [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 F] in
theorem predecessorEnd_recovery (Y : E →ₗ[F2] F)
    (R : {R : E →ₗ[F2] F // RankBelow R Y}) (x : E) :
    ((predecessorEnd Y R (Y.rangeRestrict x) : Y.range) : F) = R.val x := by
  have hq : Y.quotKerEquivRange.symm (Y.rangeRestrict x) = Y.ker.mkQ x :=
    Y.quotKerEquivRange.symm_apply_apply (Y.ker.mkQ x)
  dsimp only [predecessorEnd,LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [hq]
  rfl

omit [FiniteDimensional F2 F] in
theorem predecessorEnd_injective (Y : E →ₗ[F2] F) :
    Function.Injective (predecessorEnd Y) := by
  intro R S h
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  calc
    R.val x = ((predecessorEnd Y R (Y.rangeRestrict x) : Y.range) : F) :=
      (predecessorEnd_recovery Y R x).symm
    _ = ((predecessorEnd Y S (Y.rangeRestrict x) : Y.range) : F) :=
      congrArg (fun P : Y.range →ₗ[F2] Y.range => (P (Y.rangeRestrict x) : F)) h
    _ = S.val x := predecessorEnd_recovery Y S x

omit [FiniteDimensional F2 F] in
theorem card_predecessors_le [Finite E] [Finite F] (Y : E →ₗ[F2] F) :
    Nat.card {R : E →ₗ[F2] F // RankBelow R Y} ≤
      2 ^ (finrank F2 Y.range ^ 2) := by
  classical
  let : Finite (Y.range →ₗ[F2] Y.range) :=
    Finite.of_injective (fun f : Y.range →ₗ[F2] Y.range => (f : Y.range → Y.range))
      DFunLike.coe_injective
  have h := Nat.card_le_card_of_injective (predecessorEnd Y)
    (predecessorEnd_injective Y)
  rw [CompressionCount.natCard_linearMap] at h
  simpa only [pow_two] using h
end UniqueGamesTheorem.Appendix.TotalPredecessorCount

end

section

noncomputable section
namespace UniqueGamesTheorem.Appendix.UpperMobius
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
attribute [local instance] Classical.propDecidable
variable {W : Type*} [AddCommGroup W] [Module F2 W]
  [FiniteDimensional F2 W] [Finite W]

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.UpperMobius.quotientFinite
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.UpperMobius.dualFinite
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.UpperMobius.submoduleFinite
omit [FiniteDimensional F2 W] [Finite W] in
theorem quotient_comap_codim (K : Submodule F2 W)
    (S : Submodule F2 (W ⧸ K)) :
    Module.finrank F2 (W ⧸ S.comap K.mkQ) =
      Module.finrank F2 ((W ⧸ K) ⧸ S) := by
  let π := S.mkQ.comp K.mkQ
  have hπ : Function.Surjective π := S.mkQ_surjective.comp K.mkQ_surjective
  have hker : π.ker = S.comap K.mkQ := by simp [π, LinearMap.ker_comp]
  exact (Submodule.quotEquivOfEq _ _ hker).finrank_eq.symm.trans
    (π.quotKerEquivOfSurjective hπ).finrank_eq

omit [FiniteDimensional F2 W] [Finite W] in
theorem upperQuotientEquiv_codim (K : Submodule F2 W)
    (B : {B : Submodule F2 W // K ≤ B}) :
    Module.finrank F2 (W ⧸ B.val) =
      Module.finrank F2 ((W ⧸ K) ⧸ upperQuotientEquiv K B) := by
  have hB : (upperQuotientEquiv K B).comap K.mkQ = B.val :=
    congrArg Subtype.val ((Submodule.comapMkQRelIso K).apply_symm_apply B)
  exact (Submodule.quotEquivOfEq _ _ hB).finrank_eq.symm.trans
    (quotient_comap_codim K (upperQuotientEquiv K B))

omit [Finite W] in
theorem upperDualSubspaceEquiv_codim (K : Submodule F2 W)
    (B : {B : Submodule F2 W // K ≤ B}) :
    Module.finrank F2 (W ⧸ B.val) =
      Module.finrank F2 (upperDualSubspaceEquiv K B) := by
  calc
    _ = Module.finrank F2 ((W ⧸ K) ⧸ upperQuotientEquiv K B) :=
      upperQuotientEquiv_codim K B
    _ = Module.finrank F2 (upperQuotientEquiv K B).dualAnnihilator :=
      (Subspace.quotEquivAnnihilator (upperQuotientEquiv K B)).finrank_eq
    _ = _ := rfl

theorem upperWeightedTotal_eq_dual (K : Submodule F2 W) (w : ℕ → ℤ) :
    upperWeightedTotal K w =
      SubspaceExtensions.weightedTotal
        (K := F2) (V := Module.Dual F2 (W ⧸ K)) w := by
  classical
  let := Fintype.ofFinite {B : Submodule F2 W // K ≤ B}
  let := SubspaceExtensions.subspaceFintype (K := F2) (V := Module.Dual F2 (W ⧸ K))
  unfold upperWeightedTotal SubspaceExtensions.weightedTotal
  exact Fintype.sum_equiv (upperDualSubspaceEquiv K)
    (fun B : {B : Submodule F2 W // K ≤ B} => w (Module.finrank F2 (W ⧸ B.val)))
    (fun S : Submodule F2 (Module.Dual F2 (W ⧸ K)) => w (Module.finrank F2 S))
    (fun B => congrArg w (upperDualSubspaceEquiv_codim K B))

omit [Finite W] in
theorem quotient_finrank_zero_iff (K : Submodule F2 W) :
    Module.finrank F2 (W ⧸ K) = 0 ↔ K = ⊤ := by
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    have hr := K.finrank_quotient_add_finrank
    omega
  · intro h
    subst K
    have hr := (⊤ : Submodule F2 W).finrank_quotient_add_finrank
    rw [finrank_top] at hr
    omega

theorem binary_upper_interval_mobius (K : Submodule F2 W) :
    upperWeightedTotal K (fun r => (-1 : ℤ)^r * 2^(r.choose 2)) =
      if K = ⊤ then 1 else 0 := by
  classical
  rw [upperWeightedTotal_eq_dual]
  rw [SubspaceExtensions.binary_subspace_mobius]
  simp only [Subspace.dual_finrank_eq, quotient_finrank_zero_iff]
end UniqueGamesTheorem.Appendix.UpperMobius

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_DyadicError
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators

namespace UniqueGamesTheorem.Appendix.DyadicError

private theorem pow_le_one_aux (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    q^n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right ih hq0).trans (by simpa using hq1)

private theorem pow_antitone_aux (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (a b : ℕ) (hab : a ≤ b) : q^b ≤ q^a := by
  have hb : a + (b-a) = b :=
    (Nat.add_comm a (b-a)).trans (Nat.sub_add_cancel hab)
  calc
    q^b = q^(a+(b-a)) := congrArg (fun n : ℕ => q^n) hb.symm
    _ = q^a * q^(b-a) := by rw [pow_add]
    _ ≤ q^a * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one_aux q hq0 hq1 (b-a)) (pow_nonneg hq0 a)
    _ = q^a := mul_one _

theorem half_power_le_quarter (d n : ℕ) (hd : 1 ≤ d) :
    (1/2 : ℝ)^(3*d*n) ≤ (1/4 : ℝ)^n := by
  have h3 : 2 ≤ 3*d := le_trans (by decide : 2 ≤ 3)
    (by simpa using Nat.mul_le_mul_left 3 hd)
  have hexp : 2*n ≤ 3*d*n := Nat.mul_le_mul_right n h3
  calc
    (1/2 : ℝ)^(3*d*n) ≤ (1/2 : ℝ)^(2*n) :=
      pow_antitone_aux (1/2) (by norm_num) (by norm_num) _ _ hexp
    _ = (1/4 : ℝ)^n := by
      rw [pow_mul]
      congr 1
      norm_num

theorem quarterSum_nonneg (n : ℕ) : 0 ≤ quarterSum n := by
  unfold quarterSum
  exact Finset.sum_nonneg (fun i _ => pow_nonneg (by norm_num : (0:ℝ)≤1/4) i)

theorem quarterSum_residual (n : ℕ) :
    quarterSum n + (4/3 : ℝ)*(1/4 : ℝ)^n = 4/3 := by
  induction n with
  | zero => norm_num [quarterSum]
  | succ n ih =>
    have hstep : quarterSum (n+1) = quarterSum n + (1/4 : ℝ)^n := by
      exact Finset.sum_range_succ _ _
    rw [hstep, pow_succ]
    nlinarith

theorem quarterSum_le (n : ℕ) : quarterSum n ≤ (4/3 : ℝ) := by
  have hp : (0 : ℝ) ≤ (1/4 : ℝ)^n := pow_nonneg (by norm_num) n
  have h := quarterSum_residual n
  nlinarith

theorem quarterError_add_one (n : ℕ) (hn : 0 < n) :
    quarterError n + 1 = (quarterSum n)^2 := by
  have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr hn
  have hpair (i j : ℕ) :
      (if i=0 ∧ j=0 then (0:ℝ) else (1/4 : ℝ)^(i+j)) +
        (if i=0 ∧ j=0 then (1:ℝ) else 0) =
          (1/4 : ℝ)^i * (1/4 : ℝ)^j := by
    by_cases hi : i=0 <;> by_cases hj : j=0 <;> simp [hi,hj,pow_add]
  have hsum : quarterError n +
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        if i=0 ∧ j=0 then (1:ℝ) else 0) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (1/4 : ℝ)^i * (1/4 : ℝ)^j := by
    unfold quarterError
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact hpair i j
  have hinner (i : ℕ) :
      (∑ j ∈ Finset.range n, if i=0 ∧ j=0 then (1:ℝ) else 0) =
        if i=0 then 1 else 0 := by
    by_cases hi : i=0
    · simp [hi,h0]
    · simp [hi]
  have hdelta : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      if i=0 ∧ j=0 then (1:ℝ) else 0) = 1 := by
    simp_rw [hinner]
    simp [h0]
  have hproduct : (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      (1/4 : ℝ)^i * (1/4 : ℝ)^j) = (quarterSum n)^2 := by
    simp only [quarterSum,pow_two,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm
  rw [hdelta,hproduct] at hsum
  exact hsum

theorem quarterError_le_seven_ninths (n : ℕ) (hn : 0 < n) :
    quarterError n ≤ (7/9 : ℝ) := by
  have hbound := quarterSum_le n
  have hnonneg := quarterSum_nonneg n
  have hsq := mul_le_mul hbound hbound hnonneg (by norm_num : (0:ℝ)≤4/3)
  have hid := quarterError_add_one n hn
  nlinarith

theorem dyadicError_le_quarterError (d : ℕ) (hd : 1 ≤ d) :
    dyadicError d ≤ quarterError (d+1) := by
  unfold dyadicError quarterError
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hzero : i=0 ∧ j=0
  · simp [hzero]
  · simp only [hzero]
    exact half_power_le_quarter d (i+j) hd

theorem dyadicError_le_seven_ninths (d : ℕ) (hd : 1 ≤ d) :
    dyadicError d ≤ (7/9 : ℝ) :=
  (dyadicError_le_quarterError d hd).trans
    (quarterError_le_seven_ninths (d+1) (Nat.succ_pos d))

theorem finite_dyadic_error_le_one (d : ℕ) (hd : 1 ≤ d) :
    (∑ i ∈ Finset.range (d+1), ∑ j ∈ Finset.range (d+1),
      if i=0 ∧ j=0 then 0 else (1/2 : ℝ)^(3*d*(i+j))) ≤ 1 := by
  change dyadicError d ≤ 1
  exact (dyadicError_le_seven_ninths d hd).trans (by norm_num)

end UniqueGamesTheorem.Appendix.DyadicError

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_BadConvolution
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The signed bad-convolution term of Appendix A.1.  The selector here is
the weak image/kernel selector, prior to its separate A.4 decomposition. -/
noncomputable section
namespace UniqueGamesTheorem.Appendix.BadConvolution
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open Module (finrank)
attribute [local instance] Classical.propDecidable

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

private theorem sum_masked_eq_subtype {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] [Fintype {a // p a}] (f : α → M) :
    (∑ a, if p a then f a else 0) = ∑ a : {a // p a}, f a.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro a; simp) f

variable [Finite W] [Finite V] [FiniteDimensional F2 W] [FiniteDimensional F2 V]
variable [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)]

omit [Finite W] [Finite V] [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)] in
theorem pairDimension_eq_zero_iff (p : Submodule F2 V × Submodule F2 W) :
    pairDimension p = 0 ↔ p = (⊥,⊤) := by
  rw [pairDimension, Nat.add_eq_zero_iff]
  rw [Submodule.finrank_eq_zero, UpperMobius.quotient_finrank_zero_iff]
  constructor
  · rintro ⟨hA,hB⟩
    exact Prod.ext hA hB
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem lower_mobius_sum (I : Submodule F2 V) :
    (∑ A : Submodule F2 V, if A ≤ I then mobius (finrank F2 A) else 0) =
      if I = ⊥ then 1 else 0 := by
  let := Fintype.ofFinite {A : Submodule F2 V // A ≤ I}
  rw [sum_masked_eq_subtype]
  have h := SubmoduleInterval.binary_lower_interval_mobius I
  unfold SubmoduleInterval.lowerWeightedTotal at h
  unfold mobius
  exact_mod_cast h

theorem upper_mobius_sum (K : Submodule F2 W) :
    (∑ B : Submodule F2 W, if K ≤ B then mobius (finrank F2 (W ⧸ B)) else 0) =
      if K = ⊤ then 1 else 0 := by
  let := Fintype.ofFinite {B : Submodule F2 W // K ≤ B}
  rw [sum_masked_eq_subtype]
  have h := UpperMobius.binary_upper_interval_mobius K
  unfold UpperMobius.upperWeightedTotal at h
  unfold mobius
  exact_mod_cast h

omit [Finite W] [Finite V] [FiniteDimensional F2 W] [FiniteDimensional F2 V]
    [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)] in
private theorem triple_incidence_iff (p : Submodule F2 V × Submodule F2 W)
    (X Y : W →ₗ[F2] V) :
    (Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)) ↔
      p.1 ≤ (X.range ⊓ Y.range) ⊓ (X+Y).range ∧
        (X.ker ⊔ Y.ker) ⊔ (X+Y).ker ≤ p.2 := by
  simp only [Incidence, le_inf_iff, sup_le_iff]
  tauto

theorem triple_mobius_sum (X Y : W →ₗ[F2] V) :
    (∑ p : Submodule F2 V × Submodule F2 W,
      if Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
      then pairWeight p else 0) = if Bad X Y then 0 else 1 := by
  simp_rw [triple_incidence_iff]
  calc
    _ = (∑ A : Submodule F2 V,
        if A ≤ (X.range ⊓ Y.range) ⊓ (X+Y).range then mobius (finrank F2 A) else 0) *
        (∑ B : Submodule F2 W,
        if (X.ker ⊔ Y.ker) ⊔ (X+Y).ker ≤ B then mobius (finrank F2 (W ⧸ B)) else 0) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      by_cases hA : A ≤ (X.range ⊓ Y.range) ⊓ (X+Y).range <;>
        by_cases hB : (X.ker ⊔ Y.ker) ⊔ (X+Y).ker ≤ B <;>
        simp [pairWeight, hA, hB]
    _ = _ := by
      rw [lower_mobius_sum, upper_mobius_sum]
      by_cases hi : (X.range ⊓ Y.range) ⊓ (X+Y).range = ⊥ <;>
        by_cases hk : (X.ker ⊔ Y.ker) ⊔ (X+Y).ker = ⊤ <;>
        simp [Bad, hi, hk]

theorem signed_triple_sum (X Y : W →ₗ[F2] V) :
    (∑ p : Submodule F2 V × Submodule F2 W,
      if Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
      then signedWeight p else 0) = if Bad X Y then 1 else 0 := by
  have htop : finrank F2 (W ⧸ (⊤ : Submodule F2 W)) = 0 :=
    (UpperMobius.quotient_finrank_zero_iff ⊤).mpr rfl
  have hterm (p : Submodule F2 V × Submodule F2 W) :
      (if Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
        then pairWeight p else 0) +
      (if Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
        then signedWeight p else 0) = if p = (⊥,⊤) then 1 else 0 := by
    by_cases hp : p = (⊥,⊤)
    · subst p
      simp [Incidence, pairWeight, signedWeight, mobius, htop]
    · by_cases h : Incidence p.1 p.2 X ∧ Incidence p.1 p.2 Y ∧ Incidence p.1 p.2 (X+Y)
      all_goals simp [signedWeight, hp, h]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun p _ => hterm p)
  rw [Finset.sum_add_distrib, triple_mobius_sum] at hs
  have hdelta : (∑ p : Submodule F2 V × Submodule F2 W,
      if p = (⊥,⊤) then (1:ℝ) else 0) = 1 := by simp
  rw [hdelta] at hs
  by_cases hbad : Bad X Y <;> simp [hbad] at hs ⊢ <;> linarith

variable [Fintype (W →ₗ[F2] V)]

/-- Exact Möbius expansion; no degree or positivity assumption is used. -/
theorem badConvolution_expansion (a : (W →ₗ[F2] V) → ℝ) (X : W →ₗ[F2] V) :
    badConvolution a X =
      ∑ p : Submodule F2 V × Submodule F2 W,
        if Incidence p.1 p.2 X then signedWeight p * pieceConvolution p.1 p.2 a X else 0 := by
  calc
    _ = ∑ Y, (if Bad X Y then (1:ℝ) else 0) * (a Y * a (X+Y)) := by
      unfold badConvolution
      apply Finset.sum_congr rfl
      intro Y _
      by_cases h : Bad X Y <;> simp [h]
    _ = ∑ Y, ∑ p : Submodule F2 V × Submodule F2 W,
        if Incidence p.1 p.2 X then signedWeight p *
          (filteredCoefficient p.1 p.2 a Y * filteredCoefficient p.1 p.2 a (X+Y)) else 0 := by
      apply Finset.sum_congr rfl
      intro Y _
      rw [← signed_triple_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hX : Incidence p.1 p.2 X <;>
        by_cases hY : Incidence p.1 p.2 Y <;>
        by_cases hZ : Incidence p.1 p.2 (X+Y) <;>
        simp [filteredCoefficient, hX, hY, hZ]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hX : Incidence p.1 p.2 X
      · simp only [hX, ite_true, if_true, pieceConvolution, Finset.mul_sum]
      · simp [hX]

omit [Fintype (Submodule F2 V)] in
theorem card_lower_rank_le (I : Submodule F2 V) (n i : ℕ)
    (hn : finrank F2 I ≤ n) :
    Nat.card {A : Submodule F2 V // A ≤ I ∧ finrank F2 A = i} ≤ 2^(n*i) := by
  let : Finite (Submodule F2 I) :=
    Finite.of_injective (fun S : Submodule F2 I => (S : Set I)) SetLike.coe_injective
  let e := SubmoduleInterval.lowerIntervalEquiv I
  let code (A : {A : Submodule F2 V // A ≤ I ∧ finrank F2 A = i}) :
      {S : Submodule F2 I // finrank F2 S = i} :=
    ⟨e ⟨A.1, A.2.1⟩,
      (SubmoduleInterval.lowerInterval_finrank I ⟨A.1, A.2.1⟩).trans A.2.2⟩
  have hi : Function.Injective code := by
    intro A B h
    have he : e ⟨A.1, A.2.1⟩ = e ⟨B.1, B.2.1⟩ := congrArg Subtype.val h
    apply Subtype.ext
    exact congrArg (fun z : {A : Submodule F2 V // A ≤ I} => z.val) (e.injective he)
  exact (Nat.card_le_card_of_injective code hi).trans
    (SubspaceCounting.card_binary_subspaces_rank_le n i hn)

omit [Finite W] [Fintype (Submodule F2 W)] in
theorem card_upper_codim_le (K : Submodule F2 W) (n j : ℕ)
    (hn : finrank F2 (W ⧸ K) ≤ n) :
    Nat.card {B : Submodule F2 W // K ≤ B ∧ finrank F2 (W ⧸ B) = j} ≤ 2^(n*j) := by
  let D := Module.Dual F2 (W ⧸ K)
  let : Finite D := Finite.of_injective (Module.finBasis F2 D).equivFun
    (Module.finBasis F2 D).equivFun.injective
  let : Finite (Submodule F2 D) :=
    Finite.of_injective (fun S : Submodule F2 D => (S : Set D)) SetLike.coe_injective
  let e := UpperMobius.upperDualSubspaceEquiv K
  let code (B : {B : Submodule F2 W // K ≤ B ∧ finrank F2 (W ⧸ B) = j}) :
      {S : Submodule F2 D // finrank F2 S = j} :=
    ⟨e ⟨B.1, B.2.1⟩,
      (UpperMobius.upperDualSubspaceEquiv_codim K ⟨B.1, B.2.1⟩).symm.trans B.2.2⟩
  have hi : Function.Injective code := by
    intro B C h
    have he : e ⟨B.1, B.2.1⟩ = e ⟨C.1, C.2.1⟩ := congrArg Subtype.val h
    apply Subtype.ext
    exact congrArg (fun z : {B : Submodule F2 W // K ≤ B} => z.val) (e.injective he)
  have hdim : finrank F2 D ≤ n := by
    simpa only [D, Subspace.dual_finrank_eq] using hn
  exact (Nat.card_le_card_of_injective code hi).trans
    (SubspaceCounting.card_binary_subspaces_rank_le n j hdim)

private theorem finite_pair_level_sum {α : Type*} (s : Finset α)
    (i j : α → ℕ) (d : ℕ) (hd : 1 ≤ d)
    (hbound : ∀ a ∈ s, i a ≤ d ∧ j a ≤ d)
    (hzero : ∀ a ∈ s, ¬(i a=0 ∧ j a=0))
    (hcount : ∀ u v, (s.filter (fun a => i a=u ∧ j a=v)).card ≤ 2^(2*d*(u+v))) :
    (∑ a ∈ s, (1/2:ℝ)^(5*d*(i a+j a))) ≤ 1 := by
  classical
  have hmap : ∀ a ∈ s, (i a,j a) ∈ Finset.range (d+1) ×ˢ Finset.range (d+1) := by
    intro a ha
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound a ha).1),
       Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound a ha).2)⟩
  have hcancel (a b : ℕ) :
      (2:ℝ)^a * (1/2:ℝ)^(a+b) = (1/2:ℝ)^b := by
    rw [pow_add, ← mul_assoc, ← mul_pow]
    norm_num
  calc
    _ = ∑ u ∈ Finset.range (d+1), ∑ v ∈ Finset.range (d+1),
        ∑ a ∈ s.filter (fun a => i a=u ∧ j a=v), (1/2:ℝ)^(5*d*(i a+j a)) := by
      have h := Finset.sum_fiberwise_of_maps_to (g := fun a => (i a,j a)) hmap
        (fun a => (1/2:ℝ)^(5*d*(i a+j a)))
      simpa only [Finset.sum_product, Prod.mk.injEq] using h.symm
    _ ≤ ∑ u ∈ Finset.range (d+1), ∑ v ∈ Finset.range (d+1),
        if u=0 ∧ v=0 then 0 else (1/2:ℝ)^(3*d*(u+v)) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      by_cases hz : u=0 ∧ v=0
      · rw [ite_eq_left hz]
        have hempty : s.filter (fun a => i a=u ∧ j a=v) = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro a ha
          have ham := Finset.mem_filter.mp ha
          exact hzero a ham.1 ⟨ham.2.1.trans hz.1, ham.2.2.trans hz.2⟩
        rw [hempty, Finset.sum_empty]
      · rw [ite_eq_right hz]
        have hc : ((s.filter (fun a => i a=u ∧ j a=v)).card : ℝ) ≤
            (2:ℝ)^(2*d*(u+v)) := by exact_mod_cast hcount u v
        calc
          _ = ((s.filter (fun a => i a=u ∧ j a=v)).card : ℝ) *
              (1/2:ℝ)^(5*d*(u+v)) := by
            calc
              _ = ∑ a ∈ s.filter (fun a => i a=u ∧ j a=v), (1/2:ℝ)^(5*d*(u+v)) := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [(Finset.mem_filter.mp ha).2.1, (Finset.mem_filter.mp ha).2.2]
              _ = _ := by simp
          _ ≤ (2:ℝ)^(2*d*(u+v)) * (1/2:ℝ)^(5*d*(u+v)) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
          _ = _ := by
            have he : 5*d*(u+v)=2*d*(u+v)+3*d*(u+v) := by ring
            rw [he, hcancel]
    _ ≤ 1 := DyadicError.finite_dyadic_error_le_one d hd

omit [Finite W] [Fintype (W →ₗ[F2] V)] in
theorem incident_pair_weight_le_one (X : W →ₗ[F2] V) (d : ℕ)
    (hd : 1 ≤ d) (hX : finrank F2 X.range ≤ 2*d) :
    (∑ p : Submodule F2 V × Submodule F2 W,
      if p ≠ (⊥,⊤) ∧ p.1 ≤ X.range ∧ X.ker ≤ p.2 ∧
          finrank F2 p.1 ≤ d ∧ finrank F2 (W ⧸ p.2) ≤ d
      then (1/2:ℝ)^(5*d*(finrank F2 p.1 + finrank F2 (W ⧸ p.2))) else 0) ≤ 1 := by
  let i (p : Submodule F2 V × Submodule F2 W) := finrank F2 p.1
  let j (p : Submodule F2 V × Submodule F2 W) := finrank F2 (W ⧸ p.2)
  let good (p : Submodule F2 V × Submodule F2 W) : Prop :=
    p ≠ (⊥,⊤) ∧ p.1 ≤ X.range ∧ X.ker ≤ p.2 ∧ i p ≤ d ∧ j p ≤ d
  let s := Finset.univ.filter good
  have hs (p) (hp : p ∈ s) : good p := (Finset.mem_filter.mp hp).2
  have hbound : ∀ p ∈ s, i p ≤ d ∧ j p ≤ d := by
    intro p hp
    exact (hs p hp).2.2.2
  have hzero : ∀ p ∈ s, ¬(i p=0 ∧ j p=0) := by
    intro p hp hz
    apply (hs p hp).1
    apply (pairDimension_eq_zero_iff p).mp
    exact Nat.add_eq_zero_iff.mpr hz
  have hquot : finrank F2 (W ⧸ X.ker) ≤ 2*d := by
    have hq := X.ker.finrank_quotient_add_finrank
    have hr := X.finrank_range_add_finrank_ker
    omega
  have hcount (u v : ℕ) : (s.filter (fun p => i p=u ∧ j p=v)).card ≤ 2^(2*d*(u+v)) := by
    let t := s.filter (fun p => i p=u ∧ j p=v)
    let LA := {A : Submodule F2 V // A ≤ X.range ∧ finrank F2 A=u}
    let LB := {B : Submodule F2 W // X.ker ≤ B ∧ finrank F2 (W ⧸ B)=v}
    let code (p : ↥t) : LA × LB := by
      have hp := Finset.mem_filter.mp p.property
      have hg := hs p.val hp.1
      exact (⟨p.val.1, hg.2.1, hp.2.1⟩, ⟨p.val.2, hg.2.2.1, hp.2.2⟩)
    have hi : Function.Injective code := by
      intro p q h
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun z : LA × LB => z.1.val) h
      · exact congrArg (fun z : LA × LB => z.2.val) h
    have hc : t.card ≤ Nat.card (LA × LB) := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
        Nat.card_le_card_of_injective code hi
    calc
      _ ≤ Nat.card (LA × LB) := hc
      _ = Nat.card LA * Nat.card LB := Nat.card_prod _ _
      _ ≤ 2^((2*d)*u) * 2^((2*d)*v) := Nat.mul_le_mul
        (card_lower_rank_le X.range (2*d) u hX)
        (card_upper_codim_le X.ker (2*d) v hquot)
      _ = _ := by rw [← pow_add]; congr 1; ring
  simpa only [s, Finset.sum_filter, good, i, j] using
    finite_pair_level_sum s i j d hd hbound hzero hcount

theorem mobius_sq (i : ℕ) : (mobius i)^2 = (2:ℝ)^(2*i.choose 2) := by
  have hs : ((-1:ℝ)^i)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm i 2, pow_mul]
    norm_num
  unfold mobius
  rw [mul_pow, hs, one_mul, ← pow_mul, Nat.mul_comm]

private theorem twice_choose_two_le_square (i : ℕ) : 2*i.choose 2 ≤ i*i := by
  induction i with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

theorem mobius_pair_sq_le (d i j : ℕ) (hi : i ≤ d) (hj : j ≤ d) :
    (mobius i * mobius j)^2 ≤ (2:ℝ)^(d*(i+j)) := by
  have he : 2*i.choose 2 + 2*j.choose 2 ≤ d*(i+j) := by
    calc
      _ ≤ i*i+j*j := Nat.add_le_add (twice_choose_two_le_square i)
        (twice_choose_two_le_square j)
      _ ≤ d*i+d*j := Nat.add_le_add (Nat.mul_le_mul_right i hi) (Nat.mul_le_mul_right j hj)
      _ = _ := (Nat.mul_add d i j).symm
  have hn := Nat.pow_le_pow_right (n := 2) (by decide) he
  rw [mul_pow, mobius_sq, mobius_sq, ← pow_add]
  exact_mod_cast hn

theorem mobius_pair_weight_le (d i j : ℕ) (hi : i ≤ d) (hj : j ≤ d) :
    (mobius i * mobius j)^2 * (1/2:ℝ)^(6*d*(i+j)) ≤ (1/2:ℝ)^(5*d*(i+j)) := by
  calc
    _ ≤ (2:ℝ)^(d*(i+j)) * (1/2:ℝ)^(6*d*(i+j)) :=
      mul_le_mul_of_nonneg_right (mobius_pair_sq_le d i j hi hj) (by positivity)
    _ = _ := by
      have he : 6*d*(i+j) = d*(i+j)+5*d*(i+j) := by ring
      rw [he, pow_add, ← mul_assoc, ← mul_pow]
      norm_num

private theorem exists_nonzero_term {α : Type*} [Fintype α] (f : α → ℝ)
    (h : (∑ x, f x) ≠ 0) : ∃ x, f x ≠ 0 := by
  by_contra hn
  apply h
  apply Finset.sum_eq_zero
  intro x _
  by_contra hx
  exact hn ⟨x,hx⟩

omit [Finite W] [Finite V] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)]
    [Fintype (Submodule F2 W)] [Fintype (W →ₗ[F2] V)] in
theorem filteredCoefficient_nonzero_dimensions
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0)
    (A : Submodule F2 V) (B : Submodule F2 W) (Y : W →ₗ[F2] V)
    (h : filteredCoefficient A B a Y ≠ 0) :
    finrank F2 A ≤ d ∧ finrank F2 (W ⧸ B) ≤ d := by
  have hi : Incidence A B Y := by
    by_contra hn
    exact h (by simp [filteredCoefficient, hn])
  have hay : a Y ≠ 0 := by
    simpa only [filteredCoefficient, ite_eq_left hi] using h
  have hr : finrank F2 Y.range ≤ d := by
    by_contra hn
    exact hay (ha Y (Nat.lt_of_not_ge hn))
  have hA := Submodule.finrank_mono hi.1
  have hB := Submodule.finrank_mono hi.2
  have hq := B.finrank_quotient_add_finrank
  have hY := Y.finrank_range_add_finrank_ker
  constructor <;> omega

omit [Finite W] [Finite V] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)]
    [Fintype (Submodule F2 W)] in
theorem pieceConvolution_nonzero_dimensions
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0)
    (A : Submodule F2 V) (B : Submodule F2 W) (X : W →ₗ[F2] V)
    (h : pieceConvolution A B a X ≠ 0) :
    finrank F2 A ≤ d ∧ finrank F2 (W ⧸ B) ≤ d := by
  obtain ⟨Y,hY⟩ := exists_nonzero_term _ h
  apply filteredCoefficient_nonzero_dimensions a d ha A B Y
  intro hz
  apply hY
  rw [hz, zero_mul]

omit [Finite W] [Finite V] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)]
    [Fintype (Submodule F2 W)] [Fintype (W →ₗ[F2] V)] in
theorem rank_add_le (Y Z : W →ₗ[F2] V) :
    finrank F2 (Y+Z).range ≤ finrank F2 Y.range + finrank F2 Z.range := by
  have hle := Submodule.finrank_mono (LinearMap.range_add_le Y Z)
  have heq := Submodule.finrank_sup_add_finrank_inf_eq Y.range Z.range
  omega

omit [Finite W] [Finite V] [FiniteDimensional F2 V] [Fintype (Submodule F2 V)]
    [Fintype (Submodule F2 W)] in
theorem badConvolution_eq_zero_of_large_rank
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0)
    (X : W →ₗ[F2] V) (hX : 2*d < finrank F2 X.range) : badConvolution a X = 0 := by
  by_contra h
  obtain ⟨Y,hY⟩ := exists_nonzero_term _ h
  have hy : a Y ≠ 0 := by
    intro hz
    apply hY
    simp [hz]
  have hz : a (X+Y) ≠ 0 := by
    intro hz
    apply hY
    simp [hz]
  have hry : finrank F2 Y.range ≤ d := by
    by_contra hn
    exact hy (ha Y (Nat.lt_of_not_ge hn))
  have hrz : finrank F2 (X+Y).range ≤ d := by
    by_contra hn
    exact hz (ha (X+Y) (Nat.lt_of_not_ge hn))
  have hc : Y + (X+Y) = X := by
    calc
      _ = X + (Y+Y) := by abel
      _ = X := by rw [DegreeCover.binary_add_self, add_zero]
  have hr := rank_add_le Y (X+Y)
  rw [hc] at hr
  omega

private theorem scaled_product (c q : ℝ) (n : ℕ) :
    (c * (1/2:ℝ)^n) * ((2:ℝ)^n * q) = c*q := by
  have hc : (1/2:ℝ)^n * (2:ℝ)^n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = c * (((1/2:ℝ)^n * (2:ℝ)^n) * q) := by ring
    _ = _ := by rw [hc, one_mul]

theorem badConvolution_sq_le
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ) (hd : 1 ≤ d)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0)
    (X : W →ₗ[F2] V) (hX : finrank F2 X.range ≤ 2*d) :
    badConvolution a X ^ 2 ≤
      ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*pairDimension p) *
          pieceConvolution p.1 p.2 a X ^ 2 else 0 := by
  let good (p : Submodule F2 V × Submodule F2 W) : Prop :=
    p ≠ (⊥,⊤) ∧ p.1 ≤ X.range ∧ X.ker ≤ p.2 ∧
      finrank F2 p.1 ≤ d ∧ finrank F2 (W ⧸ p.2) ≤ d
  let s := Finset.univ.filter good
  let u (p : Submodule F2 V × Submodule F2 W) :=
    signedWeight p * (1/2:ℝ)^(3*d*pairDimension p)
  let v (p : Submodule F2 V × Submodule F2 W) :=
    (2:ℝ)^(3*d*pairDimension p) * pieceConvolution p.1 p.2 a X
  have heq : badConvolution a X = ∑ p ∈ s, u p * v p := by
    rw [badConvolution_expansion, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hg : good p
    · rw [ite_eq_left hg]
      rw [ite_eq_left (show Incidence p.1 p.2 X from ⟨hg.2.1,hg.2.2.1⟩)]
      exact (scaled_product (signedWeight p) (pieceConvolution p.1 p.2 a X)
        (3*d*pairDimension p)).symm
    · rw [ite_eq_right hg]
      by_cases hi : Incidence p.1 p.2 X
      · rw [ite_eq_left hi]
        by_cases hp : p = (⊥,⊤)
        · simp [signedWeight,hp]
        · by_cases hq : pieceConvolution p.1 p.2 a X = 0
          · rw [hq,mul_zero]
          · exact False.elim (hg ⟨hp,hi.1,hi.2,
              pieceConvolution_nonzero_dimensions a d ha p.1 p.2 X hq⟩)
      · rw [ite_eq_right hi]
  have hu : (∑ p ∈ s, u p ^ 2) ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ s, (1/2:ℝ)^(5*d*pairDimension p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hg : good p := (Finset.mem_filter.mp hp).2
        have he : (3*d*pairDimension p)*2 = 6*d*pairDimension p := by ring
        change (signedWeight p * (1/2:ℝ)^(3*d*pairDimension p))^2 ≤ _
        rw [signedWeight, ite_eq_right hg.1, mul_pow, neg_sq, ← pow_mul, he]
        exact mobius_pair_weight_le d _ _ hg.2.2.2.1 hg.2.2.2.2
      _ ≤ 1 := by
        simpa only [s,Finset.sum_filter,good,pairDimension] using
          incident_pair_weight_le_one X d hd hX
  have hv0 : 0 ≤ ∑ p ∈ s, v p ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hv : (∑ p ∈ s, v p ^ 2) ≤
      ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*pairDimension p) *
          pieceConvolution p.1 p.2 a X ^ 2 else 0 := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro p _
    by_cases hg : good p
    · rw [ite_eq_left hg, ite_eq_left hg.1]
      have he : (3*d*pairDimension p)*2 = 6*d*pairDimension p := by ring
      change ((2:ℝ)^(3*d*pairDimension p) * pieceConvolution p.1 p.2 a X)^2 ≤ _
      rw [mul_pow, ← pow_mul, he]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hn : 6*d*pairDimension p ≤ 7*d*pairDimension p :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right d (by decide : 6 ≤ 7))
      exact_mod_cast Nat.pow_le_pow_right (n := 2) (by decide) hn
    · rw [ite_eq_right hg]
      split_ifs <;> positivity
  calc
    _ = (∑ p ∈ s, u p * v p)^2 := congrArg (fun x : ℝ => x^2) heq
    _ ≤ (∑ p ∈ s, u p^2) * ∑ p ∈ s, v p^2 := Finset.sum_mul_sq_le_sq_mul_sq s u v
    _ ≤ 1 * ∑ p ∈ s, v p^2 := mul_le_mul_of_nonneg_right hu hv0
    _ = ∑ p ∈ s, v p^2 := one_mul _
    _ ≤ _ := hv

/-- The actual signed bad-convolution estimate of A.1. -/
theorem badConvolution_sq_sum_le
    (a : (W →ₗ[F2] V) → ℝ) (d : ℕ) (hd : 1 ≤ d)
    (ha : ∀ Y, d < finrank F2 Y.range → a Y = 0) :
    (∑ X, badConvolution a X ^ 2) ≤
      ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*(finrank F2 p.1 + finrank F2 (W ⧸ p.2))) *
          (∑ X, pieceConvolution p.1 p.2 a X ^ 2) else 0 := by
  calc
    _ ≤ ∑ X, ∑ p : Submodule F2 V × Submodule F2 W,
        if p ≠ (⊥,⊤) then (2:ℝ)^(7*d*pairDimension p) *
          pieceConvolution p.1 p.2 a X ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro X _
      by_cases hX : finrank F2 X.range ≤ 2*d
      · exact badConvolution_sq_le a d hd ha X hX
      · rw [badConvolution_eq_zero_of_large_rank a d ha X (Nat.lt_of_not_ge hX), zero_pow (by decide)]
        apply Finset.sum_nonneg
        intro p _
        split_ifs <;> positivity
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p = (⊥,⊤)
      · simp [hp]
      · simp [hp,pairDimension,Finset.mul_sum]

end UniqueGamesTheorem.Appendix.BadConvolution

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixNoiseLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Products and the fourth moment for the actual binary trace Fourier model. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixProducts

open scoped BigOperators
open MatrixCharacters MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]

/-- Multiplication of the real binary trace characters. -/
theorem linearTraceCharacter_re_add (S T : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    (linearTraceCharacter (S + T) X).re =
      (linearTraceCharacter S X).re * (linearTraceCharacter T X).re := by
  rw [linearTraceCharacter_add, AddChar.add_apply]
  rw [← linearTraceCharacter_real S X, ← linearTraceCharacter_real T X]
  simp

variable [Fintype (E →ₗ[F2] F)]

/-- Multiplication by a trace character translates frequency. -/
theorem linearCoeff_mul_character (f : (E →ₗ[F2] F) → ℝ)
    (S T : F →ₗ[F2] E) :
    linearCoeff (fun X => f X * (linearTraceCharacter T X).re) S =
      linearCoeff f (S + T) := by
  simp only [linearCoeff]
  apply Finset.expect_congr rfl
  intro X _
  rw [linearTraceCharacter_re_add]
  ac_rfl

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (F →ₗ[F2] E)]

/-- Products transform to counting-measure convolution of normalized coefficients. -/
theorem linearCoeff_mul (f g : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (fun X => f X * g X) S =
      ∑ T : F →ₗ[F2] E, linearCoeff f T * linearCoeff g (S + T) := by
  have hexpand : (fun X : E →ₗ[F2] F => f X * g X) =
      ∑ T : F →ₗ[F2] E, linearCoeff f T •
        (fun X => g X * (linearTraceCharacter T X).re) := by
    funext X
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc
      f X * g X =
          (∑ T : F →ₗ[F2] E, linearCoeff f T * (linearTraceCharacter T X).re) * g X := by
        rw [linear_fourier_inversion]
      _ = ∑ T : F →ₗ[F2] E,
          linearCoeff f T * (g X * (linearTraceCharacter T X).re) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro T _
        ac_rfl
  rw [hexpand, linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_mul_character]

/-- The actual fourth moment equals the squared coefficient-convolution mass. -/
theorem expect_fourth_eq_sum_convolution_sq (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, f X ^ 4) =
      ∑ S : F →ₗ[F2] E, coefficientConvolution f f S ^ 2 := by
  calc
    (𝔼 X, f X ^ 4) = 𝔼 X, (f X * f X) ^ 2 := by
      apply Finset.expect_congr rfl
      intro X _
      rw [← pow_two, ← pow_mul]
    _ = ∑ S : F →ₗ[F2] E, linearCoeff (fun X => f X * f X) S ^ 2 :=
      (linear_parseval (fun X => f X * f X)).symm
    _ = ∑ S : F →ₗ[F2] E, coefficientConvolution f f S ^ 2 := by
      simp only [linearCoeff_mul, coefficientConvolution]

end UniqueGamesTheorem.Fourier.MatrixProducts

end

end

section

/-! The actual F1 witness bound in Lemma A.1. Coefficients remain signed;
absolute values occur only in the majorant. The two predecessor counts and
Cauchy–Schwarz give the factor `2^(6*d^2)`. -/
noncomputable section
namespace UniqueGamesTheorem.Appendix.F1Energy
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankAdditivity
variable {E F : Type*} [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
local notation "G" => (E →ₗ[F2] F)
attribute [local instance] Classical.propDecidable

theorem rank_le_of_rankBelow {R Y : G} (h : RankBelow R Y) : rank R ≤ rank Y := by
  change rank Y = rank R + rank (Y - R) at h
  omega

theorem boundedSplit_rank (d : ℕ) (X : G) (R : BoundedSplit d X) : rank X ≤ 2*d := by
  have h := R.property.1
  change rank X = rank R.val + rank (X - R.val) at h
  simp only [sub_eq_add_neg, DegreeCover.binary_neg] at h
  have hR := R.property.2.1
  have hS := R.property.2.2
  omega

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
/-- The checked geometric cover supplies exactly the F1 witness condition. -/
theorem good_of_trivial_intersections (X Y : G)
    (hi : (X.range ⊓ Y.range) ⊓ (X+Y).range = ⊥)
    (hk : X.ker ⊔ Y.ker ⊔ (X+Y).ker = ⊤) : Good X Y := by
  have hc : Y + (X+Y) = X := by
    calc
      _ = X + (Y+Y) := by abel
      _ = X := by rw [DegreeCover.binary_add_self, add_zero]
  obtain ⟨R,S,C,hX,hY,hZ,hrX,hrY,hrZ⟩ :=
    DegreeCover.outside_bad_rank_cover Y (X+Y)
      (by simpa only [hc] using hi) (by simpa only [hc] using hk)
  have hXS : X = R+S := hc.symm.trans hX
  have hXR : X-R = S := by rw [hXS]; abel
  have hYR : Y-R = C := by rw [hY]; abel
  have hZS : (X+Y)-S = C := by rw [hZ]; abel
  have hSR : X+R = S := by simpa only [sub_eq_add_neg, DegreeCover.binary_neg] using hXR
  change rank (Y+(X+Y)) = rank R + rank S at hrX
  rw [hc] at hrX
  change rank Y = rank R + rank C at hrY
  change rank (X+Y) = rank S + rank C at hrZ
  refine ⟨R, ?_, ?_, ?_⟩
  · change rank X = rank R + rank (X-R)
    rw [hXR]
    exact hrX
  · change rank Y = rank R + rank (Y-R)
    rw [hYR]
    exact hrY
  · rw [hSR]
    change rank (X+Y) = rank S + rank ((X+Y)-S)
    rw [hZS]
    exact hrZ

variable [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem sum_translate (R : G) (f : G → ℝ) :
    (∑ X, f (X+R)) = ∑ X, f X := Equiv.sum_comp (translate R) f

omit [FiniteDimensional F2 F] in
theorem card_bounded_splits_le (d : ℕ) (X : G) :
    Nat.card (BoundedSplit d X) ≤ 2^(4*d^2) := by
  classical
  by_cases h : Nonempty (BoundedSplit d X)
  · have hr := boundedSplit_rank d X (Classical.choice h)
    let inc : BoundedSplit d X → {R : G // RankBelow R X} :=
      fun R => ⟨R.val, R.property.1⟩
    have hinj : Function.Injective inc := by
      intro R S hRS
      exact Subtype.ext (congrArg (fun T : {R : G // RankBelow R X} => T.val) hRS)
    have hc := Nat.card_le_card_of_injective inc hinj
    have hp := TotalPredecessorCount.card_predecessors_le X
    change Nat.card {R : G // RankBelow R X} ≤ 2^(rank X^2) at hp
    have hs : rank X^2 ≤ 4*d^2 := by nlinarith
    exact hc.trans (hp.trans (Nat.pow_le_pow_right (by decide) hs))
  · have hz : Fintype.card (BoundedSplit d X) = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun R => h ⟨R⟩⟩
    simp only [Nat.card_eq_fintype_card, hz, zero_le]

omit [FiniteDimensional F2 F] in
theorem card_predecessors_cast_le (d : ℕ) (Y : G) (hy : rank Y ≤ d) :
    (Fintype.card {R : G // RankBelow R Y} : ℝ) ≤ (2:ℝ)^(d^2) := by
  have h := TotalPredecessorCount.card_predecessors_le Y
  change Nat.card {R : G // RankBelow R Y} ≤ 2^(rank Y^2) at h
  have hs : rank Y^2 ≤ d^2 := by nlinarith
  have hp := h.trans (Nat.pow_le_pow_right (by decide) hs)
  rw [Nat.card_eq_fintype_card] at hp
  exact_mod_cast hp

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] in
theorem predecessorCoefficient_nonneg (a : G → ℝ) (R C : G) :
    0 ≤ predecessorCoefficient a R C := by
  unfold predecessorCoefficient
  split <;> positivity

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem gram_nonneg (a : G → ℝ) (R S : G) : 0 ≤ gram a R S :=
  Finset.sum_nonneg (fun C _ => mul_nonneg
    (predecessorCoefficient_nonneg a R C) (predecessorCoefficient_nonneg a S C))

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] in
theorem predecessorCoefficient_sq (a : G → ℝ) (R C : G) :
    predecessorCoefficient a R C ^ 2 =
      if RankBelow R (R+C) then a (R+C)^2 else 0 := by
  unfold predecessorCoefficient
  split <;> simp only [sq_abs, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem predecessor_energy_eq (a : G → ℝ) :
    predecessorEnergy a =
      ∑ Y, (Fintype.card {R : G // RankBelow R Y} : ℝ) * a Y^2 := by
  unfold predecessorEnergy
  calc
    _ = ∑ R, ∑ Y, if RankBelow R Y then a Y^2 else 0 := by
      apply Finset.sum_congr rfl
      intro R _
      simp only [predecessorCoefficient_sq]
      simpa only [add_comm] using
        sum_translate R (fun Y => if RankBelow R Y then a Y^2 else 0)
    _ = ∑ Y, ∑ R, if RankBelow R Y then a Y^2 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Y _
      rw [← F1Gram.sum_subtype_eq (fun R => RankBelow R Y) (fun _ => a Y^2)]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem predecessor_energy_nonneg (a : G → ℝ) : 0 ≤ predecessorEnergy a :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

omit [FiniteDimensional F2 F] in
theorem predecessor_energy_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) :
    predecessorEnergy a ≤ (2:ℝ)^(d^2) * ∑ Y, a Y^2 := by
  rw [predecessor_energy_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Y _
  by_cases hY : rank Y ≤ d
  · exact mul_le_mul_of_nonneg_right (card_predecessors_cast_le d Y hY) (sq_nonneg _)
  · rw [hdegree Y (Nat.lt_of_not_ge hY)]
    simp

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem goodConvolution_nonneg (a : G → ℝ) (X : G) : 0 ≤ goodConvolution a X := by
  apply Finset.sum_nonneg
  intro Y _
  split <;> positivity

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
/-- Each supported good term has a bounded split witness. Its summand is
counted with shared residual C=Y+R; all other summands are nonnegative. -/
theorem good_term_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (X Y : G) :
    (if Good X Y then |a Y| * |a (X+Y)| else 0) ≤
      ∑ R : BoundedSplit d X,
        predecessorCoefficient a R.val (Y+R.val) *
          predecessorCoefficient a (X+R.val) (Y+R.val) := by
  have hnonneg : 0 ≤ ∑ R : BoundedSplit d X,
      predecessorCoefficient a R.val (Y+R.val) *
        predecessorCoefficient a (X+R.val) (Y+R.val) :=
    Finset.sum_nonneg (fun R _ => mul_nonneg
      (predecessorCoefficient_nonneg a _ _) (predecessorCoefficient_nonneg a _ _))
  by_cases hg : Good X Y
  · rw [ite_eq_left hg]
    by_cases ha : a Y = 0
    · simpa only [ha, abs_zero, zero_mul] using hnonneg
    by_cases hb : a (X+Y) = 0
    · simpa only [hb, abs_zero, mul_zero] using hnonneg
    have hY : rank Y ≤ d := by
      by_contra hn
      exact ha (hdegree Y (Nat.lt_of_not_ge hn))
    have hZ : rank (X+Y) ≤ d := by
      by_contra hn
      exact hb (hdegree (X+Y) (Nat.lt_of_not_ge hn))
    obtain ⟨R,hRX,hRY,hSZ⟩ := hg
    let r : BoundedSplit d X := ⟨R,hRX,
      (rank_le_of_rankBelow hRY).trans hY, (rank_le_of_rankBelow hSZ).trans hZ⟩
    have h1 : R+(Y+R) = Y := by
      calc
        _ = (Y+R)+R := by abel
        _ = Y := add_self_cancel Y R
    have h2 : (X+R)+(Y+R) = X+Y := by
      calc
        _ = (X+Y)+(R+R) := by abel
        _ = X+Y := by rw [DegreeCover.binary_add_self, add_zero]
    have heq : predecessorCoefficient a r.val (Y+r.val) *
        predecessorCoefficient a (X+r.val) (Y+r.val) = |a Y| * |a (X+Y)| := by
      change predecessorCoefficient a R (Y+R) *
        predecessorCoefficient a (X+R) (Y+R) = _
      simp only [predecessorCoefficient, h1, h2, ite_eq_left hRY, ite_eq_left hSZ]
    rw [← heq]
    exact Finset.single_le_sum (fun (s : BoundedSplit d X) _ => mul_nonneg
      (predecessorCoefficient_nonneg a s.val (Y+s.val))
      (predecessorCoefficient_nonneg a (X+s.val) (Y+s.val)))
      (Finset.mem_univ r)
  · rw [ite_eq_right hg]
    exact hnonneg

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem goodConvolution_le_gram (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (X : G) :
    goodConvolution a X ≤ ∑ R : BoundedSplit d X, gram a R.val (X+R.val) := by
  calc
    _ ≤ ∑ Y, ∑ R : BoundedSplit d X,
        predecessorCoefficient a R.val (Y+R.val) *
          predecessorCoefficient a (X+R.val) (Y+R.val) :=
      Finset.sum_le_sum (fun Y _ => good_term_le a d hdegree X Y)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro R _
      exact sum_translate R.val (fun C =>
        predecessorCoefficient a R.val C * predecessorCoefficient a (X+R.val) C)

omit [FiniteDimensional F2 F] in
theorem goodConvolution_sq_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (X : G) :
    goodConvolution a X ^ 2 ≤ (2:ℝ)^(4*d^2) *
      ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2 := by
  have hg := goodConvolution_le_gram a d hdegree X
  have hn := goodConvolution_nonneg a X
  have hs : 0 ≤ ∑ R : BoundedSplit d X, gram a R.val (X+R.val) :=
    Finset.sum_nonneg (fun _ _ => gram_nonneg a _ _)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : BoundedSplit d X => (1:ℝ)) (fun R => gram a R.val (X+R.val))
  have hcard : (Fintype.card (BoundedSplit d X) : ℝ) ≤ (2:ℝ)^(4*d^2) := by
    have h := card_bounded_splits_le d X
    rw [Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  calc
    _ ≤ (∑ R : BoundedSplit d X, gram a R.val (X+R.val))^2 := by nlinarith
    _ ≤ (Fintype.card (BoundedSplit d X):ℝ) *
        ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2 := by simpa using hc
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem split_gram_energy_le (a : G → ℝ) (d : ℕ) :
    (∑ X, ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2) ≤
      predecessorEnergy a ^ 2 := by
  calc
    _ ≤ ∑ X, ∑ R : G, gram a R (X+R)^2 := by
      apply Finset.sum_le_sum
      intro X _
      exact F1Gram.sum_comp_le (fun R : BoundedSplit d X => R.val)
        Subtype.val_injective (fun R => gram a R (X+R)^2) (fun _ => sq_nonneg _)
    _ = ∑ R, ∑ S, gram a R S^2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro R _
      exact sum_translate R (fun S => gram a R S^2)
    _ ≤ predecessorEnergy a ^ 2 := F1Gram.gram_energy_le (predecessorCoefficient a)

omit [FiniteDimensional F2 F] in
theorem goodConvolution_energy_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) :
    (∑ X, goodConvolution a X^2) ≤ (2:ℝ)^(6*d^2) * (∑ Y, a Y^2)^2 := by
  have he := predecessor_energy_le a d hdegree
  have hn := predecessor_energy_nonneg a
  have hb : 0 ≤ (2:ℝ)^(d^2) * ∑ Y, a Y^2 := by positivity
  calc
    _ ≤ (2:ℝ)^(4*d^2) *
        ∑ X, ∑ R : BoundedSplit d X, gram a R.val (X+R.val)^2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun X _ => goodConvolution_sq_le a d hdegree X)
    _ ≤ (2:ℝ)^(4*d^2) * predecessorEnergy a^2 :=
      mul_le_mul_of_nonneg_left (split_gram_energy_le a d) (by positivity)
    _ ≤ (2:ℝ)^(4*d^2) * ((2:ℝ)^(d^2) * ∑ Y, a Y^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ = (2:ℝ)^(6*d^2) * (∑ Y, a Y^2)^2 := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
      congr 2
      omega

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
/-- The complement of any bad event covered by `Good` is bounded without
changing the signs of the coefficients in the bad part. -/
theorem abs_complement_sum_le (a : G → ℝ) (X : G) (bad : G → Prop)
    (hcover : ∀ Y, ¬ bad Y → Good X Y) :
    |∑ Y, if bad Y then 0 else a Y * a (X+Y)| ≤ goodConvolution a X := by
  calc
    _ ≤ ∑ Y, |if bad Y then 0 else a Y * a (X+Y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ goodConvolution a X := by
      apply Finset.sum_le_sum
      intro Y _
      by_cases hb : bad Y
      · simp only [ite_eq_left hb, abs_zero]
        split <;> positivity
      · simp only [ite_eq_right hb, ite_eq_left (hcover Y hb), abs_mul, le_refl]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem convolution_split_square_le (a : G → ℝ) (X : G) (bad : G → Prop)
    (hcover : ∀ Y, ¬ bad Y → Good X Y) :
    (∑ Y, a Y * a (X+Y))^2 ≤ 2 * goodConvolution a X^2 +
      2 * (∑ Y, if bad Y then a Y * a (X+Y) else 0)^2 := by
  let u : ℝ := ∑ Y, if bad Y then 0 else a Y * a (X+Y)
  let v : ℝ := ∑ Y, if bad Y then a Y * a (X+Y) else 0
  have hs : (∑ Y, a Y * a (X+Y)) = u+v := by
    dsimp only [u,v]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro Y _
    by_cases hb : bad Y <;> simp only [hb, ite_true, if_true, ite_false, add_zero, zero_add]
  have hu : |u| ≤ goodConvolution a X := abs_complement_sum_le a X bad hcover
  have hp := mul_nonneg (sub_nonneg.mpr hu)
    (add_nonneg (goodConvolution_nonneg a X) (abs_nonneg u))
  have hu2 : u^2 ≤ goodConvolution a X^2 := by nlinarith [sq_abs u]
  change (∑ Y, a Y * a (X+Y))^2 ≤ 2 * goodConvolution a X^2 + 2*v^2
  rw [hs]
  nlinarith [sq_nonneg (u-v)]

omit [FiniteDimensional F2 F] in
theorem convolution_energy_le (a : G → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) (bad : G → G → Prop)
    (hcover : ∀ X Y, ¬ bad X Y → Good X Y) :
    (∑ X, (∑ Y, a Y * a (X+Y))^2) ≤
      2 * ((2:ℝ)^(6*d^2) * (∑ Y, a Y^2)^2) +
        2 * ∑ X, (∑ Y, if bad X Y then a Y * a (X+Y) else 0)^2 := by
  calc
    _ ≤ ∑ X, (2 * goodConvolution a X^2 +
        2 * (∑ Y, if bad X Y then a Y * a (X+Y) else 0)^2) :=
      Finset.sum_le_sum (fun X _ => convolution_split_square_le a X (bad X) (hcover X))
    _ = 2 * (∑ X, goodConvolution a X^2) +
        2 * ∑ X, (∑ Y, if bad X Y then a Y * a (X+Y) else 0)^2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (goodConvolution_energy_le a d hdegree)
        (show (0:ℝ) ≤ 2 by norm_num)) le_rfl

variable [Fintype (F →ₗ[F2] E)]
open UniqueGamesTheorem.Fourier.MatrixFourier UniqueGamesTheorem.Fourier.MatrixProducts

/-- The actual fourth-moment identity reduced to the remaining signed bad
convolution. Its geometric cover is supplied by `good_of_trivial_intersections`. -/
theorem fourth_moment_le_good_bad (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E, d < rank Y → linearCoeff f Y = 0)
    (bad : (F →ₗ[F2] E) → (F →ₗ[F2] E) → Prop)
    (hcover : ∀ X Y, ¬ bad X Y → Good X Y) :
    (𝔼 X, f X^4) ≤ 2 * ((2:ℝ)^(6*d^2) * (𝔼 X, f X^2)^2) +
      2 * ∑ X, (∑ Y, if bad X Y then linearCoeff f Y * linearCoeff f (X+Y) else 0)^2 := by
  rw [expect_fourth_eq_sum_convolution_sq]
  unfold coefficientConvolution
  simpa only [linear_parseval] using
    convolution_energy_le (linearCoeff f) d hdegree bad hcover

end UniqueGamesTheorem.Appendix.F1Energy

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_WeightedFourthMoment
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The corrected weighted fourth coefficient-energy estimate of Appendix A.4.
The proof uses the actual compression-fiber energy theorem and the actual
rank-additive predecessor count, not hypotheses replacing either result.
The remaining Fourier interpretation is separate: `energy a X` is the sum of
squares of coefficients after the actual derivative compression.
-/

noncomputable section
namespace UniqueGamesTheorem.Appendix.WeightedFourthMoment

open Module
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankAdditivity (RankBelow)
attribute [local instance] Classical.propDecidable

private lemma half_cancel (a b : ℕ) :
    (2:ℝ)^a * ((2:ℝ)⁻¹)^(a+b) = ((2:ℝ)⁻¹)^b := by
  rw [pow_add, ← mul_assoc, ← mul_pow]
  norm_num

private lemma half_sum_identity (n : ℕ) :
    (∑ k ∈ Finset.range n, ((2:ℝ)⁻¹)^k) + 2*((2:ℝ)⁻¹)^n = 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    norm_num at *
    linarith

private lemma half_sum_le (n : ℕ) :
    (∑ k ∈ Finset.range n, ((2:ℝ)⁻¹)^k) ≤ 2 := by
  have hid := half_sum_identity n
  have hp : 0 ≤ ((2:ℝ)⁻¹)^n := by positivity
  linarith

private lemma finite_level_sum {α : Type*} (s : Finset α) (r : α → ℕ) (d : ℕ)
    (hdeg : ∀ x ∈ s, r x ≤ d)
    (hc : ∀ k, ((s.filter (fun x => r x=k)).card : ℝ) ≤ (2:ℝ)^(3*d*k)) :
    (∑ x ∈ s, ((2:ℝ)⁻¹)^(4*d*r x)) ≤ 2 := by
  classical
  have hmap : ∀ x ∈ s, r x ∈ Finset.range (d+1) := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hdeg x hx))
  have hone (n : ℕ) : ((2:ℝ)⁻¹)^n ≤ 1 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      have hn : 0 ≤ ((2:ℝ)⁻¹)^n := by positivity
      norm_num at *
      nlinarith
  calc
    _ = ∑ k ∈ Finset.range (d+1), ∑ x ∈ s.filter (fun x => r x=k),
        ((2:ℝ)⁻¹)^(4*d*r x) :=
      (Finset.sum_fiberwise_of_maps_to (g := r) hmap _).symm
    _ ≤ ∑ k ∈ Finset.range (d+1), ((2:ℝ)⁻¹)^k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hmul : k ≤ d*k := by
        by_cases hd : d=0
        · subst d
          have : k=0 := by omega
          simp [this]
        · have : 1 ≤ d := by omega
          simpa using Nat.mul_le_mul_right k this
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hmul
      have hdecay : ((2:ℝ)⁻¹)^(d*k) ≤ ((2:ℝ)⁻¹)^k := by
        rw [hj, pow_add]
        simpa using mul_le_mul_of_nonneg_left (hone j)
          (by positivity : 0 ≤ ((2:ℝ)⁻¹)^k)
      calc
        _ = ((s.filter (fun x => r x=k)).card : ℝ)*((2:ℝ)⁻¹)^(4*d*k) := by
          calc
            _ = ∑ x ∈ s.filter (fun x => r x=k), ((2:ℝ)⁻¹)^(4*d*k) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [(Finset.mem_filter.mp hx).2]
            _ = _ := by simp
        _ ≤ (2:ℝ)^(3*d*k)*((2:ℝ)⁻¹)^(4*d*k) :=
          mul_le_mul_of_nonneg_right (hc k) (by positivity)
        _ = ((2:ℝ)⁻¹)^(d*k) := by
          have he : 4*d*k=3*d*k+d*k := by simp only [Nat.mul_assoc]; omega
          rw [he, half_cancel]
        _ ≤ _ := hdecay
    _ ≤ 2 := half_sum_le (d+1)

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)]

/-- Sum of predecessor weights, using the actual binary linear-map count. -/
theorem predecessor_weight_sum (Y : E →ₗ[F2] F) (d : ℕ) (hd : rank Y ≤ d) :
    (∑ X ∈ Finset.univ.filter (fun X => RankBelow X Y),
      ((2:ℝ)⁻¹)^(4*d*rank X)) ≤ 2 := by
  classical
  apply finite_level_sum _ rank d
  · intro X hX
    have hp := (Finset.mem_filter.mp hX).2
    change rank Y = rank X + rank (Y-X) at hp
    omega
  · intro k
    have hneg (X : E →ₗ[F2] F) : -X = X := by
      have htwo : (1+1:F2)=0 := by decide
      have hxx : X+X=0 := by
        have h := congrArg (fun c:F2 => c • X) htwo
        simpa only [add_smul, one_smul, zero_smul] using h
      exact neg_eq_iff_add_eq_zero.mpr hxx
    have hpred (X : E →ₗ[F2] F) : RankBelow X Y ↔
        rank Y = rank X + rank (Y+X) := by
      change (rank Y = rank X + rank (Y-X)) ↔ _
      rw [sub_eq_add_neg, hneg X]
    have hc := SubspaceCounting.card_binary_predecessors_le Y d k hd
    have hn : ((Finset.univ.filter (fun X => RankBelow X Y)).filter
        (fun X => rank X=k)).card ≤ 2^(3*d*k) := by
      simp_rw [hpred]
      simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter,
        and_comm, rank] using hc
    exact_mod_cast hn

/-- Corrected Appendix A.4, in exact coefficient form, for arbitrary real
coefficients supported on maps of rank at most d. -/
theorem weighted_fourth_coefficient_energy (a : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) :
    (∑ X, ((2:ℝ)⁻¹)^(8*d*rank X)*(energy a X)^2) ≤ 2*(∑ Y, a Y^2)^2 := by
  classical
  let A : ℝ := ∑ Y, a Y^2
  let AX (X : E →ₗ[F2] F) : ℝ := ∑ Y, if RankBelow X Y then a Y^2 else 0
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hAX (X : E →ₗ[F2] F) : 0 ≤ AX X := by
    apply Finset.sum_nonneg
    intro Y _
    split_ifs <;> positivity
  have hAXA (X : E →ₗ[F2] F) : AX X ≤ A := by
    apply Finset.sum_le_sum
    intro Y _
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  have hmass : (∑ X, ((2:ℝ)⁻¹)^(4*d*rank X)*AX X) ≤ 2*A := by
    calc
      _ = ∑ Y, a Y^2 * (∑ X ∈ Finset.univ.filter (fun X => RankBelow X Y),
          ((2:ℝ)⁻¹)^(4*d*rank X)) := by
        simp only [AX, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro Y _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro X _
        split_ifs <;> ring
      _ ≤ ∑ Y, a Y^2*2 := by
        apply Finset.sum_le_sum
        intro Y _
        by_cases hy : rank Y ≤ d
        · exact mul_le_mul_of_nonneg_left (predecessor_weight_sum Y d hy) (sq_nonneg _)
        · have hz := hdegree Y (Nat.lt_of_not_ge hy)
          rw [hz]
          simp
      _ = 2*A := by rw [← Finset.sum_mul]; dsimp [A]; ring
  have hE (X : E →ₗ[F2] F) : 0 ≤ energy a X := by
    unfold energy
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcoarse (X : E →ₗ[F2] F) : energy a X ≤ (2:ℝ)^(2*d*rank X)*AX X := by
    let : Fintype (X.ker →ₗ[F2] (F ⧸ X.range)) := compressedFintype X
    have h10 := DerivativeEnergy.coefficient_energy X a d hdegree
    have he : 2*rank X*(d-rank X) ≤ 2*d*rank X := by
      calc
        _ ≤ 2*rank X*d := Nat.mul_le_mul_left _ (Nat.sub_le d (rank X))
        _ = _ := by ring
    have hn := Nat.pow_le_pow_right (n := 2) (by decide) he
    have hp : (2:ℝ)^(2*rank X*(d-rank X)) ≤ (2:ℝ)^(2*d*rank X) := by exact_mod_cast hn
    exact h10.trans (mul_le_mul_of_nonneg_right hp (hAX X))
  have hfour (X : E →ₗ[F2] F) : (energy a X)^2 ≤ (2:ℝ)^(4*d*rank X)*(A*AX X) := by
    have hs : (energy a X)^2 ≤ ((2:ℝ)^(2*d*rank X)*AX X)^2 :=
      (sq_le_sq₀ (hE X) (mul_nonneg (by positivity) (hAX X))).mpr (hcoarse X)
    have ha : (AX X)^2 ≤ A*AX X := by
      have hh := mul_le_mul_of_nonneg_right (hAXA X) (hAX X)
      simpa [pow_two] using hh
    calc
      _ ≤ ((2:ℝ)^(2*d*rank X)*AX X)^2 := hs
      _ = ((2:ℝ)^(2*d*rank X))^2*(AX X)^2 := by rw [mul_pow]
      _ ≤ ((2:ℝ)^(2*d*rank X))^2*(A*AX X) :=
        mul_le_mul_of_nonneg_left ha (sq_nonneg _)
      _ = _ := by
        rw [← pow_mul]
        congr 2
        ring
  calc
    (∑ X, ((2:ℝ)⁻¹)^(8*d*rank X)*(energy a X)^2)
        ≤ ∑ X, ((2:ℝ)⁻¹)^(4*d*rank X)*(A*AX X) := by
      apply Finset.sum_le_sum
      intro X _
      calc
        _ ≤ ((2:ℝ)⁻¹)^(8*d*rank X)*((2:ℝ)^(4*d*rank X)*(A*AX X)) :=
          mul_le_mul_of_nonneg_left (hfour X) (by positivity)
        _ = ((2:ℝ)^(4*d*rank X)*((2:ℝ)⁻¹)^(8*d*rank X))*(A*AX X) := by ring
        _ = _ := by
          have he : 8*d*rank X=4*d*rank X+4*d*rank X := by simp only [Nat.mul_assoc]; omega
          rw [he, half_cancel]
    _ = A*(∑ X, ((2:ℝ)⁻¹)^(4*d*rank X)*AX X) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro X _
      ring
    _ ≤ A*(2*A) := mul_le_mul_of_nonneg_left hmass hA
    _ = 2*A^2 := by ring

end UniqueGamesTheorem.Appendix.WeightedFourthMoment

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_RestrictionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Appendix.Restriction

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

/-- Averaging any real observable over translates of any finite parametrized
perturbation preserves its normalized mean. -/
theorem real_translation_average {G N : Type*} [AddCommGroup G] [Fintype G]
    [Fintype N] [Nonempty N] (embed : N → G) (observable : G → ℝ) :
    (𝔼 t, 𝔼 n, observable (t + embed n)) = 𝔼 t, observable t := by
  rw [Finset.expect_comm]
  calc
    _ = 𝔼 _n : N, 𝔼 t, observable t := by
      apply Finset.expect_congr rfl
      intro n _
      exact Fintype.expect_equiv (Equiv.addRight (embed n)) _ _ (fun _ => rfl)
    _ = _ := Finset.expect_const Finset.univ_nonempty _

section ActualRestrictions

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 E] in
/-- Trace compatibility on the actual quotient restriction. -/
theorem linear_trace_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (N : UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) :
    linearTracePair (UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N) Y =
      linearTracePair N (compressFrequency A B Y) := by
  unfold linearTracePair UniqueGamesTheorem.Fourier.MatrixRestrictions.embed compressFrequency
  simp only [LinearMap.comp_assoc]
  rw [LinearMap.trace_comp_comm']
  simp only [LinearMap.comp_assoc]

omit [FiniteDimensional F2 E] in
/-- The complex character identity in (A.1), on actual binary linear maps. -/
theorem linear_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) :
    linearTraceCharacter Y (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N) =
      linearTraceCharacter Y T * linearTraceCharacter (compressFrequency A B Y) N := by
  simp only [linearTraceCharacter_apply, linearTracePair_add_left,
    linear_trace_restriction, UniqueGamesTheorem.Fourier.MatrixCharacters.binarySign_add]

omit [FiniteDimensional F2 E] in
theorem real_character_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (T : E →ₗ[F2] F)
    (N : UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) :
    (linearTraceCharacter Y (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N)).re =
      (linearTraceCharacter Y T).re * (linearTraceCharacter (compressFrequency A B Y) N).re := by
  rw [linear_character_restriction, Complex.mul_re]
  simp only [linearTraceCharacter_apply,
    UniqueGamesTheorem.Fourier.MatrixCharacters.binarySign_im, mul_zero, sub_zero]

variable [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]

variable [Fintype (F →ₗ[F2] E)]

theorem linear_coefficient_merging (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) (Z : B →ₗ[F2] (E ⧸ A)) :
    linearCoeff (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T) Z =
      ∑ Y : F →ₗ[F2] E,
        if compressFrequency A B Y = Z then linearCoeff f Y * (linearTraceCharacter Y T).re
        else 0 := by
  classical
  have hexpansion : UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T =
      ∑ Y : F →ₗ[F2] E,
        (linearCoeff f Y * (linearTraceCharacter Y T).re) •
          (fun N => (linearTraceCharacter (compressFrequency A B Y) N).re) := by
    funext N
    change f (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N) = _
    rw [← linear_fourier_inversion f (T + UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B N)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro Y _
    rw [real_character_restriction]
    ring
  rw [hexpansion, linearCoeff_sum]
  apply Finset.sum_congr rfl
  intro Y _
  rw [linearCoeff_smul, linearCoeff_character]
  by_cases h : compressFrequency A B Y = Z
  · simp [h]
  · simp [h, Ne.symm h]

end ActualRestrictions

end UniqueGamesTheorem.Appendix.Restriction

end

end

section

noncomputable section
namespace UniqueGamesTheorem.Appendix.Derivatives
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem linearCoeff_spectralProjector (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (Y : F →ₗ[F2] E) :
    linearCoeff (spectralProjector P f) Y = if P Y then linearCoeff f Y else 0 := by
  classical
  unfold spectralProjector
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

theorem spectralProjector_energy (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X, spectralProjector P f X ^ 2) = ∑ Y with P Y, linearCoeff f Y ^ 2 := by
  classical
  rw [← linear_parseval, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Y _
  rw [linearCoeff_spectralProjector]
  split_ifs <;> simp

theorem function_eq_of_linearCoeff_eq {f g : (E →ₗ[F2] F) → ℝ}
    (h : ∀ Y, linearCoeff f Y = linearCoeff g Y) : f = g := by
  funext M
  rw [← linear_fourier_inversion f M, ← linear_fourier_inversion g M]
  apply Finset.sum_congr rfl
  intro Y _
  rw [h Y]

theorem spectralProjector_comp (P Q : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector P (spectralProjector Q f) =
      spectralProjector (fun Y => P Y ∧ Q Y) f := by
  classical
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [linearCoeff_spectralProjector]
  by_cases hP : P Y <;> by_cases hQ : Q Y <;> simp [hP, hQ]

theorem selector_energy_sum {I : Type*} [Fintype I]
    (P : I → (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) :
    (∑ i : I, 𝔼 X, spectralProjector (P i) f X ^ 2) =
      ∑ Y : F →ₗ[F2] E, (selectorMultiplicity P Y : ℝ) * linearCoeff f Y ^ 2 := by
  classical
  simp_rw [spectralProjector_energy, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Y _
  calc
    (∑ i : I, if P i Y then linearCoeff f Y ^ 2 else 0) =
        ∑ i : I with P i Y, linearCoeff f Y ^ 2 := by rw [Finset.sum_filter]
    _ = _ := by simp [selectorMultiplicity]

theorem selector_energy_sum_le {I : Type*} [Fintype I]
    (P : I → (F →ₗ[F2] E) → Prop) (f : (E →ₗ[F2] F) → ℝ) (M : ℝ)
    (hcount : ∀ Y : F →ₗ[F2] E, linearCoeff f Y ≠ 0 →
      (selectorMultiplicity P Y : ℝ) ≤ M) :
    (∑ i : I, 𝔼 X, spectralProjector (P i) f X ^ 2) ≤ M * (𝔼 X, f X ^ 2) := by
  classical
  rw [selector_energy_sum, ← linear_parseval, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Y _
  by_cases hY : linearCoeff f Y = 0
  · simp [hY]
  · exact mul_le_mul_of_nonneg_right (hcount Y hY) (sq_nonneg _)

variable [Finite E] [Finite F]

theorem linearCoeff_mapDerivative (X : F →ₗ[F2] E)
    [Fintype (X.ker →ₗ[F2] (E ⧸ X.range))]
    (f : (E →ₗ[F2] F) → ℝ) (Z : X.ker →ₗ[F2] (E ⧸ X.range)) :
    linearCoeff (mapDerivative X f) Z =
      ∑ Y : F →ₗ[F2] E,
        if RankAdditivity.RankBelow X Y ∧
            Restriction.compressFrequency X.range X.ker Y = Z then linearCoeff f Y else 0 := by
  classical
  unfold mapDerivative
  rw [Restriction.linear_coefficient_merging]
  apply Finset.sum_congr rfl
  intro Y _
  simp only [rankProjector, linearCoeff_spectralProjector]
  have hp : (linearTraceCharacter Y (0 : E →ₗ[F2] F)).re = 1 := by simp
  rw [hp]
  by_cases hR : RankAdditivity.RankBelow X Y <;>
    by_cases hC : Restriction.compressFrequency X.range X.ker Y = Z <;> simp [hR, hC]

theorem mapDerivative_energy_eq_coefficients (X : F →ₗ[F2] E)
    [Fintype (X.ker →ₗ[F2] (E ⧸ X.range))]
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 N, mapDerivative X f N ^ 2) =
      ∑ Z : X.ker →ₗ[F2] (E ⧸ X.range),
        (∑ Y : F →ₗ[F2] E, if RankAdditivity.RankBelow X Y ∧
          Restriction.compressFrequency X.range X.ker Y = Z then linearCoeff f Y else 0) ^ 2 := by
  rw [← linear_parseval]
  simp_rw [linearCoeff_mapDerivative]

/-- The coefficient-energy definition from the weighted estimate is exactly
the normalized squared norm of the actual map derivative. -/
theorem mapDerivative_energy_eq_weighted_energy (X : F →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 N, mapDerivative X f N ^ 2) = WeightedFourthMoment.energy (linearCoeff f) X := by
  let := WeightedFourthMoment.compressedFintype X
  rw [mapDerivative_energy_eq_coefficients]
  unfold WeightedFourthMoment.energy
  simp only [Restriction.compressFrequency, FullCompression.compression]
  congr 1

/-- The corrected weighted fourth-moment estimate for genuine derivative
norms, with the normalized primal measure and counting frequency measure. -/
theorem weighted_fourth_derivative_energy (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (∑ X : F →ₗ[F2] E, ((2 : ℝ)⁻¹) ^ (8 * d * Module.finrank F2 X.range) *
      (𝔼 N, mapDerivative X f N ^ 2) ^ 2) ≤ 2 * (𝔼 M, f M ^ 2) ^ 2 := by
  calc
    _ = ∑ X : F →ₗ[F2] E, ((2 : ℝ)⁻¹) ^ (8 * d * Module.finrank F2 X.range) *
        WeightedFourthMoment.energy (linearCoeff f) X ^ 2 := by
      apply Finset.sum_congr rfl
      intro X _
      rw [mapDerivative_energy_eq_weighted_energy]
    _ ≤ _ := by
      simpa only [linear_parseval] using
        WeightedFourthMoment.weighted_fourth_coefficient_energy (linearCoeff f) d hdegree

theorem spectralProjector_restriction (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (Q : (B →ₗ[F2] (E ⧸ A)) → Prop) (f : (E →ₗ[F2] F) → ℝ)
    (T : E →ₗ[F2] F) :
    spectralProjector Q (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T) =
      UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict
        (spectralProjector (fun Y => Q (Restriction.compressFrequency A B Y)) f) A B T := by
  classical
  apply function_eq_of_linearCoeff_eq
  intro Z
  rw [linearCoeff_spectralProjector,
    Restriction.linear_coefficient_merging, Restriction.linear_coefficient_merging]
  by_cases hQ : Q Z
  · simp only [ite_eq_left hQ]
    apply Finset.sum_congr rfl
    intro Y _
    rw [linearCoeff_spectralProjector]
    by_cases hC : Restriction.compressFrequency A B Y = Z <;> simp [hC, hQ]
  · simp only [ite_eq_right hQ]
    symm
    apply Finset.sum_eq_zero
    intro Y _
    rw [linearCoeff_spectralProjector]
    by_cases hC : Restriction.compressFrequency A B Y = Z <;> simp [hC, hQ]

theorem spectralProjector_restriction_moment_average
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (Q : (B →ₗ[F2] (E ⧸ A)) → Prop) (f : (E →ₗ[F2] F) → ℝ)
    {N : Type*} [Fintype N] [Nonempty N]
    (θ : N → UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter A B) (p : ℕ) :
    (𝔼 T, 𝔼 n, spectralProjector Q
      (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T) (θ n) ^ p) =
      𝔼 M, spectralProjector (fun Y => Q (Restriction.compressFrequency A B Y)) f M ^ p := by
  simp_rw [spectralProjector_restriction]
  exact Restriction.real_translation_average
    (fun n => UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B (θ n))
    (fun M => spectralProjector (fun Y => Q (Restriction.compressFrequency A B Y)) f M ^ p)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem hybridDerivative_energy_average (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, 𝔼 N, hybridDerivative A B T f N ^ 2) =
      𝔼 X, hybridProjector A B f X ^ 2 :=
  Restriction.real_translation_average (UniqueGamesTheorem.Fourier.MatrixRestrictions.embed A B)
    (fun X => hybridProjector A B f X ^ 2)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem hybridMomentSum_le_of_uniform_energy (d : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (ζ : ℝ)
    (hζ : ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
      UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B ≤ d →
        (𝔼 N, hybridDerivative A B T f N ^ 2) ≤ ζ) :
    hybridMomentSum d f ≤ ζ * hybridSelectorEnergy d f := by
  classical
  unfold hybridMomentSum hybridSelectorEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc
    (𝔼 T, (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) ^ 2) ≤
        𝔼 T, ζ * (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) := by
      apply Finset.expect_le_expect
      intro T _
      have hn : 0 ≤ 𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2 :=
        Finset.expect_nonneg (fun N _ => sq_nonneg _)
      simpa only [pow_two] using
        mul_le_mul_of_nonneg_right (hζ s.val.1 s.val.2 T s.property) hn
    _ = ζ * (𝔼 T, 𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) :=
      (Finset.mul_expect _ _ _).symm
    _ = ζ * (𝔼 X, hybridProjector s.val.1 s.val.2 f X ^ 2) := by
      rw [hybridDerivative_energy_average]

end UniqueGamesTheorem.Appendix.Derivatives

end

end

section

noncomputable section
namespace UniqueGamesTheorem.Appendix.A1Reduction
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier UniqueGamesTheorem.Fourier.MatrixProducts
open UniqueGamesTheorem.Appendix.Derivatives
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F] in
theorem weakFourthSum_nonneg (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    0 ≤ weakFourthSum d f := by
  apply Finset.sum_nonneg
  intro p _
  split
  · exact mul_nonneg (by positivity) (Finset.expect_nonneg (fun _ _ => by positivity))
  · exact le_rfl

omit [Finite E] [Finite F] [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)] in
theorem linearCoeff_weakProjector (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) (Y : F →ₗ[F2] E) :
    linearCoeff (spectralProjector (fun Z => A ≤ Z.range ∧ Z.ker ≤ B) f) Y =
      BadConvolution.filteredCoefficient A B (linearCoeff f) Y := by
  simp only [linearCoeff_spectralProjector, BadConvolution.filteredCoefficient,
    BadConvolution.Incidence]
  rfl

omit [Finite E] [Finite F] [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)] in
/-- Actual Parseval/product identity for each signed weakly selected piece. -/
theorem piece_fourth_moment (A : Submodule F2 E) (B : Submodule F2 F)
    (f : (E →ₗ[F2] F) → ℝ) :
    (∑ X : F →ₗ[F2] E, BadConvolution.pieceConvolution A B (linearCoeff f) X^2) =
      𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M^4 := by
  rw [expect_fourth_eq_sum_convolution_sq]
  simp only [coefficientConvolution, BadConvolution.pieceConvolution,
    linearCoeff_weakProjector]

omit [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)] in
theorem actual_bad_cover (X Y : F →ₗ[F2] E) (hbad : ¬ BadConvolution.Bad X Y) :
    F1Energy.Good X Y := by
  apply F1Energy.good_of_trivial_intersections X Y
  · by_contra hi
    exact hbad (Or.inl hi)
  · by_contra hk
    exact hbad (Or.inr hk)

omit [FiniteDimensional F2 E] [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)]
  [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)] in
theorem badConvolution_zero_of_degree_zero (a : (F →ₗ[F2] E) → ℝ)
    (ha : ∀ Y, 0 < Module.finrank F2 Y.range → a Y = 0) (X : F →ₗ[F2] E) :
    BadConvolution.badConvolution a X = 0 := by
  classical
  unfold BadConvolution.badConvolution
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hY : Y = 0
  · subst Y
    by_cases hX : X = 0
    · subst X
      simp [BadConvolution.Bad]
    · have hz := ha X (DegreeZero.rank_pos_of_ne_zero X hX)
      simp [hz]
  · have hz := ha Y (DegreeZero.rank_pos_of_ne_zero Y hY)
    simp [hz]

theorem badConvolution_energy_le_weakFourthSum (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (∑ X : F →ₗ[F2] E, BadConvolution.badConvolution (linearCoeff f) X^2) ≤
      weakFourthSum d f := by
  by_cases hd : d = 0
  · subst d
    have hz : ∀ X, BadConvolution.badConvolution (linearCoeff f) X = 0 :=
      badConvolution_zero_of_degree_zero (linearCoeff f) hdegree
    simpa only [hz, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      Finset.sum_const_zero] using weakFourthSum_nonneg 0 f
  · have h := BadConvolution.badConvolution_sq_sum_le (linearCoeff f) d (by omega) hdegree
    simpa only [weakFourthSum, piece_fourth_moment] using h

theorem fourth_moment_le_two (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (𝔼 M, f M^4) ≤ 2 * ((2:ℝ)^(6*d^2) * (𝔼 M, f M^2)^2) +
      2 * weakFourthSum d f := by
  have hcore : (𝔼 M, f M^4) ≤ 2 * ((2:ℝ)^(6*d^2) * (𝔼 M, f M^2)^2) +
      2 * ∑ X : F →ₗ[F2] E, BadConvolution.badConvolution (linearCoeff f) X^2 := by
    simpa only [BadConvolution.badConvolution] using
      F1Energy.fourth_moment_le_good_bad f d hdegree BadConvolution.Bad actual_bad_cover
  exact hcore.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (badConvolution_energy_le_weakFourthSum f d hdegree) (show (0:ℝ) ≤ 2 by norm_num)))

/-- Lemma A.1, Equation (A.6), for every degree d including zero. -/
theorem degree_reduction (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y : F →ₗ[F2] E,
      d < Module.finrank F2 Y.range → linearCoeff f Y = 0) :
    (𝔼 M, f M^4) / 162 ≤ (2:ℝ)^(6*d^2) * (𝔼 M, f M^2)^2 + weakFourthSum d f := by
  have h := fourth_moment_le_two f d hdegree
  have ha : 0 ≤ (2:ℝ)^(6*d^2) * (𝔼 M, f M^2)^2 := by positivity
  have hb := weakFourthSum_nonneg d f
  apply (div_le_iff₀ (show (0:ℝ) < 162 by norm_num)).mpr
  nlinarith

end UniqueGamesTheorem.Appendix.A1Reduction

end

end

section

/-! Actual Fourier degree loss for both derivative operators. The support
cutoffs apply to genuine binary linear maps, including the case where the
total derivative order is larger than the original degree. -/

noncomputable section
namespace UniqueGamesTheorem.Appendix.DerivativeDegree

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem DegreeAtMost.mono {d e : ℕ} {f : (E →ₗ[F2] F) → ℝ}
    (hf : DegreeAtMost d f) (hde : d ≤ e) : DegreeAtMost e f := by
  intro Y hY
  exact hf Y (lt_of_le_of_lt hde hY)

theorem eq_zero_of_linearCoeff_zero {f : (E →ₗ[F2] F) → ℝ}
    (hf : ∀ Y, linearCoeff f Y = 0) : f = 0 := by
  funext M
  rw [← linear_fourier_inversion f M]
  simp [hf]

variable [Finite E] [Finite F]

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.DerivativeDegree.quotientFinite
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.DerivativeDegree.compressedDualFintype
theorem hybridDerivative_coeff_zero_of_lt (A : Submodule F2 E)
    (B : Submodule F2 F) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (Z : B →ₗ[F2] (E ⧸ A))
    (hZ : d < frequencyRank Z + order A B) :
    linearCoeff (hybridDerivative A B T f) Z = 0 := by
  unfold hybridDerivative
  rw [Restriction.linear_coefficient_merging]
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hc : Restriction.compressFrequency A B Y = Z
  · rw [ite_eq_left hc]
    unfold hybridProjector
    rw [linearCoeff_spectralProjector]
    by_cases hY : LinearIdentities.Hybrid Y A B
    · rw [ite_eq_left hY]
      have hr := Level.LinearRank.hybrid_rank_loss A B Y hY.1 hY.2
      have he : Level.LinearRank.compress A B Y = Z := by
        simpa only [Level.LinearRank.compress, Restriction.compressFrequency,
          LinearMap.comp_assoc] using hc
      rw [he] at hr
      have hr' : frequencyRank Z + order A B = frequencyRank Y := by
        simpa only [frequencyRank, order, Nat.add_assoc] using hr
      have hdY : d < frequencyRank Y := hZ.trans_eq hr'
      rw [hf Y hdY, zero_mul]
    · rw [ite_eq_right hY, zero_mul]
  · rw [ite_eq_right hc]

theorem degree_hybridDerivative (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) {d : ℕ} (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    DegreeAtMost (d - order A B) (hybridDerivative A B T f) := by
  intro Z hZ
  exact hybridDerivative_coeff_zero_of_lt A B T f hf Z (by omega)

theorem hybridDerivative_eq_zero_of_lt_order (A : Submodule F2 E)
    (B : Submodule F2 F) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B) : hybridDerivative A B T f = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  exact hybridDerivative_coeff_zero_of_lt A B T f hf Z (by omega)

theorem mapDerivative_coeff_zero_of_lt (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (Z : X.ker →ₗ[F2] (E ⧸ X.range))
    (hZ : d < frequencyRank Z + frequencyRank X) :
    linearCoeff (mapDerivative X f) Z = 0 := by
  rw [linearCoeff_mapDerivative]
  apply Finset.sum_eq_zero
  intro Y _
  by_cases hY : RankAdditivity.RankBelow X Y ∧
      Restriction.compressFrequency X.range X.ker Y = Z
  · rw [ite_eq_left hY]
    have hc : FullCompression.compression X Y = Z := by
      simpa only [FullCompression.compression, Restriction.compressFrequency] using hY.2
    have hr := FullCompression.fiber_rank X Z
      (⟨Y, hY.1, hc⟩ : FullCompression.Fiber X Z)
    apply hf Y
    unfold frequencyRank at *
    change Module.finrank F2 Y.range =
      Module.finrank F2 X.range + Module.finrank F2 Z.range at hr
    omega
  · rw [ite_eq_right hY]

theorem degree_mapDerivative (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    DegreeAtMost (d - frequencyRank X) (mapDerivative X f) := by
  intro Z hZ
  exact mapDerivative_coeff_zero_of_lt X f hf Z (by omega)

theorem mapDerivative_eq_zero_of_lt_rank (X : F →ₗ[F2] E) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < frequencyRank X) : mapDerivative X f = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  exact mapDerivative_coeff_zero_of_lt X f hf Z (by omega)

theorem mapDerivative_zero (X : F →ₗ[F2] E) :
    mapDerivative X (0 : (E →ₗ[F2] F) → ℝ) = 0 := by
  apply eq_zero_of_linearCoeff_zero
  intro Z
  rw [linearCoeff_mapDerivative]
  simp [linearCoeff]

theorem degree_map_hybridDerivative (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    DegreeAtMost (d - (order A B + frequencyRank X))
      (mapDerivative X (hybridDerivative A B T f)) := by
  simpa only [Nat.sub_sub] using
    degree_mapDerivative X (hybridDerivative A B T f)
      (degree_hybridDerivative A B T f hf)

/-- The support cutoff keeps the total order intact even when `order A B > d`. -/
theorem map_hybridDerivative_eq_zero_of_lt_order_rank
    (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (T : E →ₗ[F2] F) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B + Module.finrank F2 X.range) :
    mapDerivative X (hybridDerivative A B T f) = 0 := by
  by_cases hAB : d < order A B
  · rw [hybridDerivative_eq_zero_of_lt_order A B T f hf hAB, mapDerivative_zero]
  · apply mapDerivative_eq_zero_of_lt_rank X (hybridDerivative A B T f)
      (degree_hybridDerivative A B T f hf)
    unfold frequencyRank
    omega

theorem map_hybridDerivative_fourth_average_eq_zero_of_lt_order_rank
    (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) {d : ℕ}
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (h : d < order A B + Module.finrank F2 X.range) :
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) = 0 := by
  simp_rw [map_hybridDerivative_eq_zero_of_lt_order_rank A B X _ f hf h]
  simp

end UniqueGamesTheorem.Appendix.DerivativeDegree

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_OperatorPartitions
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Actual Fourier-projector partitions for Appendix A.4 and A.5

The partitions use the proved unique geometric selectors on each actual
Fourier index. Their finite index types are the canonical counting types.
-/

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Appendix.Derivatives

namespace UniqueGamesTheorem.Appendix.OperatorPartitions

attribute [local instance] Classical.propDecidable

private theorem indicator_eq_sum_of_unique {I : Type*} [Fintype I]
    (P : Prop) (R : I → Prop) (a : ℝ)
    (hpart : P → ∃! i, R i) (hback : ∀ i, R i → P) :
    (if P then a else 0) = ∑ i, if R i then a else 0 := by
  classical
  by_cases hp : P
  · obtain ⟨i, hi, hu⟩ := hpart hp
    rw [ite_eq_left hp]
    symm
    calc
      (∑ j, if R j then a else 0) = if R i then a else 0 := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          exact ite_eq_right (fun hj => hji (hu j hj))
        · simp
      _ = a := ite_eq_left hi
  · rw [ite_eq_right hp]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => hp (hback i hi))

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem spectralProjector_partition {I : Type*} [Fintype I]
    (P : (F →ₗ[F2] E) → Prop) (R : I → (F →ₗ[F2] E) → Prop)
    (hpart : ∀ Y, P Y → ∃! i, R i Y)
    (hback : ∀ i Y, R i Y → P Y) (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector P f = ∑ i, spectralProjector (R i) f := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  rw [linearCoeff_spectralProjector, linearCoeff_sum]
  simp only [linearCoeff_spectralProjector]
  exact indicator_eq_sum_of_unique (P Y) (fun i => R i Y)
    (linearCoeff f Y) (hpart Y) (fun i => hback i Y)

variable [Finite E] [Finite F]

theorem spectralProjector_restriction_projector
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (B →ₗ[F2] (E ⧸ A))]
    (P : (F →ₗ[F2] E) → Prop)
    (Q : (B →ₗ[F2] (E ⧸ A)) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) :
    spectralProjector Q
      (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict (spectralProjector P f) A B T) =
    UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict
      (spectralProjector (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) f)
      A B T := by
  have hp : (fun Y => Q (Restriction.compressFrequency A B Y) ∧ P Y) =
      (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) := by
    funext Y
    exact propext and_comm
  rw [spectralProjector_restriction, spectralProjector_comp, hp]

open UniqueGamesTheorem.Appendix.LinearIdentities
open UniqueGamesTheorem.Appendix.RankAdditivity

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F] in
theorem a4Mask_unique (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) (hY : A ≤ Y.range ∧ Y.ker ≤ B) :
    ∃! i : A4GeometricIndex A B, a4Mask A B i Y := by
  obtain ⟨p, hp, hu⟩ := (BinaryA4.a4_unique_selector Y A B).mp hY
  rcases hp with ⟨hA, hB, hinner, hker, hrange, hrank⟩
  let i : A4GeometricIndex A B := ⟨p, hA, hB, hker, hrange⟩
  refine ⟨i, ⟨hinner, hrank⟩, ?_⟩
  intro j hj
  apply Subtype.ext
  apply hu
  rcases j.property with ⟨hjA, hjB, hjker, hjrange⟩
  exact ⟨hjA, hjB, hj.1, hjker, hjrange, hj.2⟩

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F] in
theorem a4Mask_implies_weak (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A4GeometricIndex A B) (Y : F →ₗ[F2] E)
    (hi : a4Mask A B i Y) : A ≤ Y.range ∧ Y.ker ≤ B := by
  rcases i.property with ⟨_, _, hker, hrange⟩
  exact a4_weak_selector_of_summand Y i.val.1 A B i.val.2.1 i.val.2.2
    hi.1 hker hrange hi.2

omit [Finite E] [Finite F] in
theorem a4_projector_partition (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f =
      ∑ i : A4GeometricIndex A B, spectralProjector (a4Mask A B i) f := by
  exact spectralProjector_partition _ _
    (a4Mask_unique A B) (a4Mask_implies_weak A B) f

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F] in
theorem a5Mask_unique (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    (Y : F →ₗ[F2] E) (hY : a5OuterMask X A B Y) :
    ∃! i : A5GeometricIndex X A B, a5Mask X A B i Y := by
  obtain ⟨p, hp, hu⟩ := (a5_unique_selector X Y A B hI hB).mp hY
  rcases hp with ⟨hinner, hdis, hA, hcover, hmeet, hlocal⟩
  let i : A5GeometricIndex X A B := ⟨p, hdis, hA, hcover, hmeet⟩
  refine ⟨i, ⟨hinner, hlocal⟩, ?_⟩
  intro j hj
  apply Subtype.ext
  apply hu
  rcases j.property with ⟨hjdis, hjA, hjcover, hjmeet⟩
  exact ⟨hj.1, hjdis, hjA, hjcover, hjmeet, hj.2⟩

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F] in
theorem a5Mask_implies_outer (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A5GeometricIndex X A B) (Y : F →ₗ[F2] E)
    (hi : a5Mask X A B i Y) : a5OuterMask X A B Y := by
  rcases i.property with ⟨hdis, hA, hcover, hmeet⟩
  exact ⟨rankBelow_of_compressed_rankBelow X Y i.val.1 i.val.2
      hi.1 hdis hcover hi.2,
    reverse_outer_hybrid X Y i.val.1 A B i.val.2
      hi.1 hdis hA hcover hmeet hi.2⟩

omit [Finite E] [Finite F] in
theorem a5_projector_partition (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    [Fintype (A5GeometricIndex X A B)] (f : (E →ₗ[F2] F) → ℝ) :
    spectralProjector (a5OuterMask X A B) f =
      ∑ i : A5GeometricIndex X A B, spectralProjector (a5Mask X A B i) f := by
  exact spectralProjector_partition _ _
    (a5Mask_unique X A B hI hB) (a5Mask_implies_outer X A B) f

end UniqueGamesTheorem.Appendix.OperatorPartitions

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_A5IndexCount
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The actual forward Appendix A.5 index injects into two spaces of linear
maps. The first map recovers the image complement, the second its kernel
complement. No index-cardinality inequality is assumed. -/

noncomputable section

namespace UniqueGamesTheorem.Appendix.A5IndexCount

open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {V W : Type*}
  [AddCommGroup V] [Module F2 V] [AddCommGroup W] [Module F2 W]

theorem projectionA0_injective (A I A0 A0' : Submodule F2 V) (hIA : I ≤ A)
    (hd : Disjoint A0 I) (hj : A0 ⊔ I = A)
    (hd' : Disjoint A0' I) (hj' : A0' ⊔ I = A)
    (h : projectionA0 A I A0 hIA hd hj = projectionA0 A I A0' hIA hd' hj') :
    A0 = A0' := by
  let P := I.comap A.subtype
  let Q : {Q : Submodule F2 A // IsCompl P Q} :=
    ⟨A0.comap A.subtype, internal_isCompl A I A0 hIA hd hj⟩
  let Q' : {Q : Submodule F2 A // IsCompl P Q} :=
    ⟨A0'.comap A.subtype, internal_isCompl A I A0' hIA hd' hj'⟩
  have hp : (P.isComplEquivProj Q).val = (P.isComplEquivProj Q').val := by
    apply LinearMap.ext
    intro a
    apply (insideEquiv A I hIA).injective
    exact LinearMap.congr_fun h a
  have hQ := P.isComplEquivProj.injective (Subtype.ext hp)
  have hq : A0.comap A.subtype = A0'.comap A.subtype := congrArg Subtype.val hQ
  have hA0 : A0 ≤ A := le_sup_left.trans hj.le
  have hA0' : A0' ≤ A := le_sup_left.trans hj'.le
  ext x
  constructor
  · intro hx
    have hm : (⟨x, hA0 hx⟩ : A) ∈ A0.comap A.subtype := hx
    rw [hq] at hm
    exact hm
  · intro hx
    have hm : (⟨x, hA0' hx⟩ : A) ∈ A0'.comap A.subtype := hx
    rw [← hq] at hm
    exact hm

theorem fullRange_surjective {U L : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup L] [Module F2 L] (S : U →ₗ[F2] L) (hS : S.range = ⊤) :
    Function.Surjective (fullRange S hS) := fun c => ⟨c.val, Subtype.ext rfl⟩

theorem range_sectionB0 (B J B0 : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B) :
    (sectionB0 B J B0 hc hm).range = (A4IndexCount.quotientRestriction B B0).range := by
  rw [sectionB0, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (fullRange_surjective _ _))]
  exact A4IndexCount.factorViaRange_range _ _ _

theorem recover_sectionB0 (B J B0 : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B) :
    (sectionB0 B J B0 hc hm).range.comap B.mkQ = B0 := by
  rw [range_sectionB0]
  have hB : B ≤ B0 := hm.symm.le.trans inf_le_left
  ext w
  change B.mkQ w ∈ (A4IndexCount.quotientRestriction B B0).range ↔ w ∈ B0
  constructor
  · rintro ⟨b, hb⟩
    change B.mkQ (b : W) = B.mkQ w at hb
    have hz : w - (b : W) ∈ B := by
      apply (Submodule.Quotient.mk_eq_zero B).mp
      change B.mkQ (w - (b : W)) = 0
      rw [map_sub, hb, sub_self]
    simpa only [sub_add_cancel] using B0.add_mem (hB hz) b.property
  · intro hw
    exact ⟨⟨w, hw⟩, rfl⟩

theorem sectionB0_injective (B J B0 B0' : Submodule F2 W)
    (hc : B0 ⊔ J = ⊤) (hm : B0 ⊓ J = B)
    (hc' : B0' ⊔ J = ⊤) (hm' : B0' ⊓ J = B)
    (h : sectionB0 B J B0 hc hm = sectionB0 B J B0' hc' hm') : B0 = B0' := by
  calc
    B0 = (sectionB0 B J B0 hc hm).range.comap B.mkQ :=
      (recover_sectionB0 B J B0 hc hm).symm
    _ = (sectionB0 B J B0' hc' hm').range.comap B.mkQ :=
      congrArg (fun T : (W ⧸ J) →ₗ[F2] (W ⧸ B) => T.range.comap B.mkQ) h
    _ = B0' := recover_sectionB0 B J B0' hc' hm'

theorem encode_injective (X : W →ₗ[F2] V) (A : Submodule F2 V) (B : Submodule F2 W)
    (hIA : X.range ≤ A) : Function.Injective (encode X A B hIA) := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext
  · exact projectionA0_injective A X.range p.val.1 q.val.1 hIA
      p.property.1 p.property.2.1 q.property.1 q.property.2.1 (congrArg Prod.fst h)
  · exact sectionB0_injective B X.ker p.val.2 q.val.2
      p.property.2.2.1 p.property.2.2.2 q.property.2.2.1 q.property.2.2.2
      (congrArg Prod.snd h)

variable [FiniteDimensional F2 V] [FiniteDimensional F2 W]

theorem card_geometricIndex_le (X : W →ₗ[F2] V)
    (A : Submodule F2 V) (B : Submodule F2 W) (hIA : X.range ≤ A) :
    Nat.card (OperatorPartitions.A5GeometricIndex X A B) ≤
      2 ^ (Module.finrank F2 X.range *
        (Module.finrank F2 A + Module.finrank F2 (W ⧸ B))) := by
  have hfirst := CompressionCount.natCard_linearMap (U := A) (C := X.range)
  have hsecond := CompressionCount.natCard_linearMap (U := W ⧸ X.ker) (C := W ⧸ B)
  let : Finite (A →ₗ[F2] X.range) := Nat.finite_of_card_ne_zero
    (by rw [hfirst]; exact pow_ne_zero _ (by decide))
  let : Finite ((W ⧸ X.ker) →ₗ[F2] (W ⧸ B)) := Nat.finite_of_card_ne_zero
    (by rw [hsecond]; exact pow_ne_zero _ (by decide))
  have h := Nat.card_le_card_of_injective (encode X A B hIA) (encode_injective X A B hIA)
  rw [Nat.card_prod, hfirst, hsecond, X.quotKerEquivRange.finrank_eq, ← pow_add] at h
  have he : Module.finrank F2 A * Module.finrank F2 X.range +
      Module.finrank F2 X.range * Module.finrank F2 (W ⧸ B) =
      Module.finrank F2 X.range *
        (Module.finrank F2 A + Module.finrank F2 (W ⧸ B)) := by ring
  rwa [he] at h

theorem card_geometricIndex_degree_le (X : W →ₗ[F2] V)
    (A : Submodule F2 V) (B : Submodule F2 W) (hIA : X.range ≤ A) (d : Nat)
    (hA : Module.finrank F2 A ≤ d) (hB : Module.finrank F2 (W ⧸ B) ≤ d) :
    Nat.card (OperatorPartitions.A5GeometricIndex X A B) ≤
      2 ^ (2 * d * Module.finrank F2 X.range) := by
  have hs : Module.finrank F2 A + Module.finrank F2 (W ⧸ B) ≤ 2 * d := by omega
  have he : Module.finrank F2 X.range *
      (Module.finrank F2 A + Module.finrank F2 (W ⧸ B)) ≤
      2 * d * Module.finrank F2 X.range := by
    calc
      _ ≤ Module.finrank F2 X.range * (2 * d) := Nat.mul_le_mul_left _ hs
      _ = _ := by ac_rfl
  exact (card_geometricIndex_le X A B hIA).trans
    (Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2) he)

theorem card_geometricIndex_cube_le (X : W →ₗ[F2] V)
    (A : Submodule F2 V) (B : Submodule F2 W) (hIA : X.range ≤ A) (d : Nat)
    (hA : Module.finrank F2 A ≤ d) (hB : Module.finrank F2 (W ⧸ B) ≤ d) :
    Nat.card (OperatorPartitions.A5GeometricIndex X A B) ^ 3 ≤
      2 ^ (6 * d * Module.finrank F2 X.range) := by
  have h := Nat.pow_le_pow_left (card_geometricIndex_degree_le X A B hIA d hA hB) 3
  rw [← pow_mul] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end UniqueGamesTheorem.Appendix.A5IndexCount

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_A5ReverseIndex
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.A5ReverseIndex

open UniqueGamesTheorem.Integration.BinaryLinear
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W : Type*} [AddCommGroup V] [Module F2 V]
  [AddCommGroup W] [Module F2 W]

theorem relativeFrequency_rank (A A' : Submodule F2 V)
    (B' B : Submodule F2 W) (hA : A ≤ A') (hB : B' ≤ B)
    (Y : B' →ₗ[F2] (V ⧸ A')) :
    Module.finrank F2 (relativeFrequency A A' B' B hA hB Y).range =
      Module.finrank F2 Y.range :=
  CoordinateTransport.finrank_range_transport
    (SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩)
    (Submodule.quotientQuotientEquivQuotient A A' hA).symm Y

variable [FiniteDimensional F2 V] [FiniteDimensional F2 W]

theorem relative_codomain_dimension (A A' : Submodule F2 V) (hA : A ≤ A') :
    Module.finrank F2 (A'.map A.mkQ) + Module.finrank F2 A =
      Module.finrank F2 A' := by
  have h₁ := (A'.map A.mkQ).finrank_quotient_add_finrank
  have h₂ := A.finrank_quotient_add_finrank
  have h₃ := A'.finrank_quotient_add_finrank
  have h₄ := (Submodule.quotientQuotientEquivQuotient A A' hA).finrank_eq
  omega

theorem relative_domain_codimension_le (B' B : Submodule F2 W) (hB : B' ≤ B) :
    Module.finrank F2 (B ⧸ B'.comap B.subtype) ≤
      Module.finrank F2 (W ⧸ B') := by
  have h₁ := (B'.comap B.subtype).finrank_quotient_add_finrank
  have h₂ := B'.finrank_quotient_add_finrank
  have h₃ := B.finrank_le
  have h₄ := (SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).finrank_eq
  change Module.finrank F2 B' = Module.finrank F2 (B'.comap B.subtype) at h₄
  omega

/-- Each fixed earlier pair contributes at most two graph-parameter budgets. -/
theorem card_local_antecedent_le (A A' : Submodule F2 V)
    (B' B : Submodule F2 W) (hA : A ≤ A') (hB : B' ≤ B)
    (Y : B' →ₗ[F2] (V ⧸ A')) (d k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hAd : Module.finrank F2 A' ≤ d)
    (hBd : Module.finrank F2 (W ⧸ B') ≤ d) :
    Nat.card (AntecedentCount.Antecedent
      (B'.comap B.subtype) (A'.map A.mkQ)
      (relativeFrequency A A' B' B hA hB Y)) ≤ 2 ^ (2 * d * k) := by
  apply AntecedentCount.card_antecedent_le
  · simpa only [relativeFrequency_rank] using hY
  · have h := relative_codomain_dimension A A' hA
    omega
  · exact (relative_domain_codimension_le B' B hB).trans hBd

local instance quotientFinite {U : Type*} [AddCommGroup U] [Module F2 U]
    [Finite U] (P : Submodule F2 U) : Finite (U ⧸ P) :=
  Finite.of_surjective P.mkQ P.mkQ_surjective

local instance linearMapFinite {U Z : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup Z] [Module F2 Z] [Finite U] [Finite Z] :
    Finite (U →ₗ[F2] Z) :=
  Finite.of_injective (fun f : U →ₗ[F2] Z => (f : U → Z)) DFunLike.coe_injective

private theorem card_sigma_le {I : Type*} [Fintype I]
    (fiber : I → Type*) [∀ i, Finite (fiber i)] (N : ℕ)
    (h : ∀ i, Nat.card (fiber i) ≤ N) :
    Nat.card (Σ i, fiber i) ≤ Nat.card I * N := by
  rw [Nat.card_sigma]
  calc
    (∑ i, Nat.card (fiber i)) ≤ ∑ _i : I, N := Finset.sum_le_sum (fun i _ => h i)
    _ = Nat.card I * N := by simp [Nat.card_eq_fintype_card]

variable [Finite V] [Finite W]
variable [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)]

/-- Sharp graph-based upper bound for the entire actual reverse fiber. -/
theorem card_ancestor_le (A' : Submodule F2 V) (B' : Submodule F2 W)
    (Y : B' →ₗ[F2] (V ⧸ A')) (d i j k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hA : Module.finrank F2 A' ≤ d)
    (hB : Module.finrank F2 (W ⧸ B') ≤ d) :
    Nat.card (Ancestor A' B' Y i j) ≤ 2 ^ (d * (i + j) + 2 * d * k) := by
  have hlocal (A : EarlierA A' i) (B : EarlierB B' j) :=
    card_local_antecedent_le A.val A' B' B.val A.property.1 B.property.1
      Y d k hY hA hB
  have hinner (A : EarlierA A' i) :
      Nat.card (Σ B : EarlierB B' j,
        AntecedentCount.Antecedent (B'.comap B.val.subtype) (A'.map A.val.mkQ)
          (relativeFrequency A.val A' B' B.val A.property.1 B.property.1 Y)) ≤
        Nat.card (EarlierB B' j) * 2 ^ (2 * d * k) :=
    card_sigma_le _ _ (hlocal A)
  have htotal : Nat.card (Ancestor A' B' Y i j) ≤
      Nat.card (EarlierA A' i) * (Nat.card (EarlierB B' j) * 2 ^ (2 * d * k)) :=
    card_sigma_le _ _ hinner
  calc
    Nat.card (Ancestor A' B' Y i j) ≤
        Nat.card (EarlierA A' i) * (Nat.card (EarlierB B' j) * 2 ^ (2 * d * k)) := htotal
    _ ≤ 2 ^ (d * i) * (2 ^ (d * j) * 2 ^ (2 * d * k)) :=
      Nat.mul_le_mul (BadConvolution.card_lower_rank_le A' d i hA)
        (Nat.mul_le_mul_right _ (BadConvolution.card_upper_codim_le B' d j hB))
    _ = 2 ^ (d * (i + j) + 2 * d * k) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring

theorem card_ancestor_le_source (A' : Submodule F2 V) (B' : Submodule F2 W)
    (Y : B' →ₗ[F2] (V ⧸ A')) (d i j k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hA : Module.finrank F2 A' ≤ d)
    (hB : Module.finrank F2 (W ⧸ B') ≤ d) (ht : i + j + k ≤ d) :
    Nat.card (Ancestor A' B' Y i j) ≤ 2 ^ (3 * (d * (i + j + k))) := by
  apply (card_ancestor_le A' B' Y d i j k hY hA hB).trans
  apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
  have h := Induction.antecedent_exponent_budget d i j k (i + j + k) rfl ht
  calc
    d * (i + j) + 2 * d * k ≤ d * (i + j) + 2 * d * k + k * k :=
      Nat.le_add_right _ _
    _ ≤ 3 * (d * (i + j + k)) := by simpa only [Nat.mul_assoc] using h

end

end UniqueGamesTheorem.Appendix.A5ReverseIndex

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_RestrictionTransport
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem

/-!
# Exact transport of nested affine restrictions

The nested quotient-domain/range inclusion has exactly the effective
annihilator and target obtained by comap and map. Its parameterization is
linearly equivalent to the direct effective restriction, independently of
any Fourier frequency. Thus normalized second moments and the outer average
of their squares agree while retaining the full affine translate.
-/

noncomputable section

namespace Appendix.RestrictionTransport

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions

section Nested

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem nestedEmbedding_injective (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    Function.Injective (nestedEmbedding A B C D) := by
  intro N N' h
  apply embed_injective C D
  apply embed_injective A B
  exact h

/-- Exact effective annihilator and target of a nested restriction. -/
theorem exists_nested_embed_iff (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) (M : E →ₗ[F2] F) :
    (∃ N : Parameter C D, nestedEmbedding A B C D N = M) ↔
      C.comap A.mkQ ≤ M.ker ∧ M.range ≤ D.map B.subtype := by
  constructor
  · rintro ⟨N, rfl⟩
    constructor
    · intro x hx
      change (embed C D N (A.mkQ x) : F) = 0
      have hz : embed C D N (A.mkQ x) = 0 := embed_vanishes C D N hx
      rw [hz]
      rfl
    · rintro y ⟨x, rfl⟩
      apply Submodule.mem_map.mpr
      refine ⟨embed C D N (A.mkQ x), ?_, rfl⟩
      exact embed_range C D N ⟨A.mkQ x, rfl⟩
  · rintro ⟨hker, hrange⟩
    have hA : A ≤ M.ker := by
      intro x hx
      apply hker
      change A.mkQ x ∈ C
      have hz : A.mkQ x = 0 := by simpa using hx
      rw [hz]
      exact C.zero_mem
    have hB : M.range ≤ B := by
      intro y hy
      obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp (hrange hy)
      exact b.property
    obtain ⟨N, hN⟩ := (exists_embed_iff A B M).mpr ⟨hA, hB⟩
    have hC : C ≤ N.ker := by
      intro q hq
      obtain ⟨x, rfl⟩ := A.mkQ_surjective q
      change N (A.mkQ x) = 0
      apply Subtype.ext
      change embed A B N x = 0
      rw [hN]
      exact hker hq
    have hD : N.range ≤ D := by
      rintro b ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := A.mkQ_surjective q
      have hm : M x ∈ D.map B.subtype := hrange ⟨x, rfl⟩
      have hco : (N (A.mkQ x) : F) = M x := congrArg (fun L : E →ₗ[F2] F => L x) hN
      rw [← hco] at hm
      obtain ⟨b, hb, heq⟩ := Submodule.mem_map.mp hm
      have heq' : b = N (A.mkQ x) := Subtype.ext heq
      exact heq' ▸ hb
    obtain ⟨P, hP⟩ := (exists_embed_iff C D N).mpr ⟨hC, hD⟩
    refine ⟨P, ?_⟩
    change embed A B (embed C D P) = M
    rw [hP, hN]

/-- Nested and effective direct restrictions describe exactly the same perturbations. -/
theorem nested_range_eq (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    (nestedEmbedding A B C D).range =
      (embedding (C.comap A.mkQ) (D.map B.subtype)).range := by
  ext M
  change (∃ N, nestedEmbedding A B C D N = M) ↔
    (∃ N, embed (C.comap A.mkQ) (D.map B.subtype) N = M)
  rw [exists_nested_embed_iff, exists_embed_iff]

end Nested

section SameRange

variable {K : Type*} {G : Type*} {P : Type*} {Q : Type*} [Field K]
  [AddCommGroup G] [Module K G] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]

theorem sameRangeEquiv_commutes (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (x : P) :
    g (sameRangeEquiv f g hf hg h x) = f x := by
  exact Classical.choose_spec (exists_range_preimage f g (le_of_eq h) x)

variable [Fintype P] [Fintype Q]

/-- Injective parameter changes preserve normalized uniform expectations. -/
theorem expect_eq_of_same_range (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (observable : G → ℝ) :
    (𝔼 x, observable (f x)) = 𝔼 y, observable (g y) := by
  exact Fintype.expect_equiv (sameRangeEquiv f g hf hg h).toEquiv _ _
    (fun x => congrArg observable (sameRangeEquiv_commutes f g hf hg h x).symm)

/-- Preserve second moments at the same full ambient translate. -/
theorem restriction_secondMoment_eq_of_same_range
    (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (observable : G → ℝ) (T : G) :
    (𝔼 x, observable (T + f x) ^ 2) = 𝔼 y, observable (T + g y) ^ 2 :=
  expect_eq_of_same_range f g hf hg h (fun z => observable (T + z) ^ 2)

end SameRange

end Appendix.RestrictionTransport

namespace Appendix.LinearIdentities

variable {K : Type*} {W : Type*} {V : Type*} [Field K]
  [AddCommGroup W] [AddCommGroup V] [Module K W] [Module K V]

/-- A subspace disjoint from the image has exactly the original kernel as preimage. -/
theorem a5_preimage_eq_ker (X : W →ₗ[K] V) (A₀ : Submodule K V)
    (hd : Disjoint A₀ (LinearMap.range X)) : A₀.comap X = LinearMap.ker X := by
  ext w
  constructor
  · intro hw
    exact Submodule.disjoint_def.mp hd (X w) hw ⟨w, rfl⟩
  · intro hw
    change X w ∈ A₀
    rw [show X w = 0 from hw]
    exact A₀.zero_mem

/-- Restricting to a subspace that covers the domain modulo the kernel preserves the image. -/
theorem a5_range_domRestrict_eq_of_cover (X : W →ₗ[K] V) (B₀ : Submodule K W)
    (hc : B₀ ⊔ LinearMap.ker X = ⊤) :
    LinearMap.range (X.domRestrict B₀) = LinearMap.range X := by
  apply le_antisymm (LinearMap.range_domRestrict_le_range X B₀)
  rintro v ⟨w, hw⟩
  have ht : w ∈ B₀ ⊔ LinearMap.ker X := by rw [hc]; trivial
  rcases Submodule.mem_sup.mp ht with ⟨b, hb, k, hk, hbk⟩
  refine ⟨⟨b, hb⟩, ?_⟩
  change X b = v
  rw [← hw, ← hbk, map_add, show X k = 0 from hk, add_zero]

/-- The A.5 compressed image pulls back to its exact effective annihilator. -/
theorem a5_effective_annihilator (X : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B₀ : Submodule K W)
    (hA : A₀ ⊔ LinearMap.range X = A)
    (hc : B₀ ⊔ LinearMap.ker X = ⊤) :
    (LinearMap.range (compress X A₀ B₀)).comap A₀.mkQ = A := by
  rw [compress, LinearMap.range_comp, a5_range_domRestrict_eq_of_cover X B₀ hc,
    Submodule.comap_map_mkQ, hA]

/-- The A.5 compressed kernel maps to its exact effective codomain. -/
theorem a5_effective_codomain (X : W →ₗ[K] V)
    (A₀ : Submodule K V) (B B₀ : Submodule K W)
    (hd : Disjoint A₀ (LinearMap.range X))
    (hB : B₀ ⊓ LinearMap.ker X = B) :
    (LinearMap.ker (compress X A₀ B₀)).map B₀.subtype = B := by
  rw [compress, LinearMap.ker_comp, Submodule.ker_mkQ]
  change ((A₀.comap X).comap B₀.subtype).map B₀.subtype = B
  rw [a5_preimage_eq_ker X A₀ hd, Submodule.map_comap_subtype, hB]

end Appendix.LinearIdentities

end

end UniqueGamesTheorem

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_HybridCompositionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Genuine hybrid derivative composition: the effective subspaces have
additive order, and the full translate average preserves the square of the
second moment. Transport of an additional map derivative is a separate step. -/

noncomputable section
namespace UniqueGamesTheorem.Appendix.HybridComposition

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives UniqueGamesTheorem.Appendix.LinearIdentities
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
variable [Finite E] [Finite F]

local instance quotientFinite_r6cf1fa_1 (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective
local instance compressedDualFintype_r6cf1fa_1 (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (B →ₗ[F2] (E ⧸ A)) := by
  classical
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype (E ⧸ A) := Fintype.ofFinite _
  exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) => (L : B → E ⧸ A))
    DFunLike.coe_injective
omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem effective_hybrid_iff (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) (Y : F →ₗ[F2] E) :
    (Hybrid Y A B ∧ Hybrid (Restriction.compressFrequency A B Y) C D) ↔
      Hybrid Y (C.comap A.mkQ) (D.map B.subtype) := by
  have hA : A ≤ C.comap A.mkQ := by
    intro x hx
    change A.mkQ x ∈ C
    have hz : A.mkQ x = 0 := by
      change x ∈ LinearMap.ker A.mkQ
      simpa only [Submodule.ker_mkQ] using hx
    rw [hz]
    exact C.zero_mem
  have hB : D.map B.subtype ≤ B := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact y.property
  have hC : (C.comap A.mkQ).map A.mkQ = C := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := A.mkQ_surjective x
      exact Submodule.mem_map.mpr ⟨y, hx, rfl⟩
  have hD : (D.map B.subtype).comap B.subtype = D := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp hx
      have hxy : y = x := Subtype.ext heq
      simpa only [hxy] using hy
    · intro hx
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  have hh := LinearIdentities.nested_hybrid_iff Y A (C.comap A.mkQ)
    (D.map B.subtype) B hA hB
  rw [hC, hD] at hh
  have hc : Restriction.compressFrequency A B Y = LinearIdentities.compress Y A B := by
    ext x
    rfl
  simpa only [hc] using hh

omit [Finite E] in
theorem finrank_comap_mkQ (A : Submodule F2 E)
    (C : Submodule F2 (E ⧸ A)) :
    Module.finrank F2 (C.comap A.mkQ) = Module.finrank F2 A + Module.finrank F2 C := by
  let P := C.comap A.mkQ
  have hAP : A ≤ P := by
    intro x hx
    change A.mkQ x ∈ C
    have hz : A.mkQ x = 0 := by
      change x ∈ LinearMap.ker A.mkQ
      simpa only [Submodule.ker_mkQ] using hx
    rw [hz]
    exact C.zero_mem
  let q : P →ₗ[F2] (E ⧸ A) := A.mkQ.comp P.subtype
  have hR : q.range = C := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      obtain ⟨y, hy⟩ := A.mkQ_surjective x
      refine ⟨⟨y, ?_⟩, ?_⟩
      · change A.mkQ y ∈ C
        rw [hy]
        exact hx
      · exact hy
  have hK : q.ker.map P.subtype = A := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      have hz : (y : E) ∈ LinearMap.ker A.mkQ := hy
      change (y : E) ∈ A
      simpa only [Submodule.ker_mkQ] using hz
    · intro hx
      refine Submodule.mem_map.mpr ⟨⟨x, hAP hx⟩, ?_, rfl⟩
      change x ∈ LinearMap.ker A.mkQ
      simpa only [Submodule.ker_mkQ] using hx
  have hKdim := Submodule.finrank_map_subtype_eq P q.ker
  rw [hK] at hKdim
  have hdim := q.finrank_range_add_finrank_ker
  rw [hR, ← hKdim] at hdim
  change Module.finrank F2 P = Module.finrank F2 A + Module.finrank F2 C
  omega

omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem order_effective (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    order (C.comap A.mkQ) (D.map B.subtype) = order A B + order C D := by
  have hA := finrank_comap_mkQ A C
  have hD := Submodule.finrank_map_subtype_eq B D
  have hFB := B.finrank_quotient_add_finrank
  have hBD := D.finrank_quotient_add_finrank
  have hFbar := (D.map B.subtype).finrank_quotient_add_finrank
  change Module.finrank F2 (C.comap A.mkQ) +
      Module.finrank F2 (F ⧸ D.map B.subtype) =
    (Module.finrank F2 A + Module.finrank F2 (F ⧸ B)) +
      (Module.finrank F2 C + Module.finrank F2 (B ⧸ D))
  omega

end UniqueGamesTheorem.Appendix.HybridComposition

end

end

section

/-!
# Native derivative norm decompositions for Appendix A.4 and A.5

The finite projector partitions and exact affine restriction transport yield
norm bounds for the actual derivative operators. The cardinality factors are
explicit: numerical estimates on the geometric index sets are separate lemmas.
-/

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.OperatorPartitions
open UniqueGamesTheorem.Appendix.LinearIdentities
open UniqueGamesTheorem.Appendix.RankAdditivity

namespace UniqueGamesTheorem.Appendix.OperatorNorm

theorem energy_sum_sq_le_card_cube {I Ω : Type*} [Fintype I] [Fintype Ω]
    (g : I → Ω → ℝ) :
    (𝔼 n, (∑ i, g i n) ^ 2) ^ 2 ≤
      (Fintype.card I : ℝ) ^ 3 * ∑ i, (𝔼 n, g i n ^ 2) ^ 2 := by
  classical
  let e : I → ℝ := fun i => 𝔼 n, g i n ^ 2
  let E : ℝ := 𝔼 n, (∑ i, g i n) ^ 2
  let N : ℝ := Fintype.card I
  have hE : 0 ≤ E := Finset.expect_nonneg fun _ _ => sq_nonneg _
  have he (i : I) : 0 ≤ e i := Finset.expect_nonneg fun _ _ => sq_nonneg _
  have hs : 0 ≤ ∑ i, e i := Finset.sum_nonneg fun i _ => he i
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hp (n : Ω) : (∑ i, g i n) ^ 2 ≤ N * ∑ i, g i n ^ 2 := by
    simpa [N] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : I => (1 : ℝ)) (fun i => g i n))
  have hEbound : E ≤ N * ∑ i, e i := by
    calc
      E ≤ 𝔼 n, N * ∑ i, g i n ^ 2 :=
        Finset.expect_le_expect fun n _ => hp n
      _ = N * ∑ i, e i := by
        rw [← Finset.mul_expect, Finset.expect_sum_comm]
  have hsq : E ^ 2 ≤ (N * ∑ i, e i) ^ 2 :=
    (sq_le_sq₀ hE (mul_nonneg hN hs)).mpr hEbound
  have hcs : (∑ i, e i) ^ 2 ≤ N * ∑ i, e i ^ 2 := by
    simpa [N] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun _ : I => (1 : ℝ)) e)
  change E ^ 2 ≤ N ^ 3 * ∑ i, e i ^ 2
  calc
    E ^ 2 ≤ N ^ 2 * (∑ i, e i) ^ 2 := by simpa [mul_pow] using hsq
    _ ≤ N ^ 2 * (N * ∑ i, e i ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg N)
    _ = N ^ 3 * ∑ i, e i ^ 2 := by ring

theorem fourth_sum_le_card_cube {I : Type*} [Fintype I] (a : I → ℝ) :
    (∑ i, a i) ^ 4 ≤ (Fintype.card I : ℝ) ^ 3 * ∑ i, a i ^ 4 := by
  have h := energy_sum_sq_le_card_cube (Ω := Unit) (fun i _ => a i)
  simpa [← pow_mul] using h

theorem average_fourth_sum_le_card_cube {I Ω : Type*} [Fintype I] [Fintype Ω]
    (g : I → Ω → ℝ) :
    (𝔼 n, (∑ i, g i n) ^ 4) ≤
      (Fintype.card I : ℝ) ^ 3 * ∑ i, 𝔼 n, g i n ^ 4 := by
  calc
    (𝔼 n, (∑ i, g i n) ^ 4) ≤
        𝔼 n, (Fintype.card I : ℝ) ^ 3 * ∑ i, g i n ^ 4 :=
      Finset.expect_le_expect fun n _ => fourth_sum_le_card_cube (fun i => g i n)
    _ = (Fintype.card I : ℝ) ^ 3 * ∑ i, 𝔼 n, g i n ^ 4 := by
      rw [← Finset.mul_expect, Finset.expect_sum_comm]

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.OperatorNorm.quotientFinite
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.OperatorNorm.compressedDualFintype
omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem compressFrequency_eq_compress (A : Submodule F2 E) (B : Submodule F2 F)
    (Y : F →ₗ[F2] E) : Restriction.compressFrequency A B Y = compress Y A B := by
  ext x
  rfl

theorem nested_projector_restriction_apply
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (P : (F →ₗ[F2] E) → Prop) (Q : (B →ₗ[F2] (E ⧸ A)) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F)
    (S : MatrixRestrictions.Parameter A B) (N : MatrixRestrictions.Parameter C D) :
    MatrixRestrictions.restrict
      (spectralProjector Q (MatrixRestrictions.restrict (spectralProjector P f) A B T))
      C D S N =
    spectralProjector (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) f
      (T + MatrixRestrictions.embed A B S + RestrictionTransport.nestedEmbedding A B C D N) := by
  classical
  rw [OperatorPartitions.spectralProjector_restriction_projector]
  let g := spectralProjector (fun Y => P Y ∧ Q (Restriction.compressFrequency A B Y)) f
  change g (T + (MatrixRestrictions.embedding A B)
      (S + MatrixRestrictions.embed C D N)) =
    g ((T + (MatrixRestrictions.embedding A B) S) +
      (MatrixRestrictions.embedding A B) (MatrixRestrictions.embed C D N))
  rw [map_add, add_assoc]

theorem a5_outer_energy (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    (f : (E →ₗ[F2] F) → ℝ) (S : MatrixRestrictions.Parameter X.range X.ker) :
    (𝔼 N, hybridDerivative (A.map X.range.mkQ) (B.comap X.ker.subtype)
      S (mapDerivative X f) N ^ 2) =
    𝔼 M : MatrixRestrictions.Parameter A B,
      spectralProjector (a5OuterMask X A B) f
        (MatrixRestrictions.embed X.range X.ker S + MatrixRestrictions.embed A B M) ^ 2 := by
  classical
  let C := A.map X.range.mkQ
  let D := B.comap X.ker.subtype
  let g := spectralProjector (a5OuterMask X A B) f
  let t := MatrixRestrictions.embed X.range X.ker S
  have hp (N : MatrixRestrictions.Parameter C D) :
      hybridDerivative C D S (mapDerivative X f) N =
        g (t + RestrictionTransport.nestedEmbedding X.range X.ker C D N) := by
    have hm : (fun Y => RankBelow X Y ∧ Hybrid (compress Y X.range X.ker) C D) =
        a5OuterMask X A B := rfl
    have hh := nested_projector_restriction_apply X.range X.ker C D
      (fun Y => RankBelow X Y) (fun Y => Hybrid Y C D) f 0 S N
    simp only [compressFrequency_eq_compress] at hh
    rw [hm] at hh
    simpa only [hybridDerivative, hybridProjector, mapDerivative, rankProjector,
      g, t, zero_add] using hh
  calc
    (𝔼 N, hybridDerivative C D S (mapDerivative X f) N ^ 2) =
        𝔼 N, g (t + RestrictionTransport.nestedEmbedding X.range X.ker C D N) ^ 2 :=
      Finset.expect_congr rfl fun N _ => congrArg (fun r : ℝ => r ^ 2) (hp N)
    _ = 𝔼 M : MatrixRestrictions.Parameter A B,
        g (t + MatrixRestrictions.embed A B M) ^ 2 := by
      have ha : C.comap X.range.mkQ = A := by
        dsimp only [C]
        rw [Submodule.comap_map_mkQ, sup_of_le_right hI]
      have hb : D.map X.ker.subtype = B := by
        dsimp only [D]
        rw [Submodule.map_comap_subtype, inf_eq_right.mpr hB]
      have hrange : (RestrictionTransport.nestedEmbedding X.range X.ker C D).range =
          (MatrixRestrictions.embedding A B).range := by
        rw [RestrictionTransport.nested_range_eq, ha, hb]
      have htransport := RestrictionTransport.restriction_secondMoment_eq_of_same_range
        (K := F2) (P := MatrixRestrictions.Parameter C D)
        (Q := MatrixRestrictions.Parameter A B) (G := E →ₗ[F2] F)
        (RestrictionTransport.nestedEmbedding X.range X.ker C D)
        (MatrixRestrictions.embedding A B)
        (RestrictionTransport.nestedEmbedding_injective X.range X.ker C D)
        (MatrixRestrictions.embed_injective A B) hrange g t
      simpa only [MatrixRestrictions.embedding, LinearMap.coe_mk, AddHom.coe_mk] using htransport

theorem a5_summand_energy (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (i : A5GeometricIndex X A B)
    (f : (E →ₗ[F2] F) → ℝ) (S : MatrixRestrictions.Parameter X.range X.ker) :
    (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
      (hybridDerivative i.val.1 i.val.2
        (MatrixRestrictions.embed X.range X.ker S) f) N ^ 2) =
    𝔼 M : MatrixRestrictions.Parameter A B,
      spectralProjector (a5Mask X A B i) f
        (MatrixRestrictions.embed X.range X.ker S + MatrixRestrictions.embed A B M) ^ 2 := by
  classical
  let A0 := i.val.1
  let B0 := i.val.2
  let Z := compress X A0 B0
  let g := spectralProjector (a5Mask X A B i) f
  let t := MatrixRestrictions.embed X.range X.ker S
  rcases i.property with ⟨hdis, hA, hcover, hmeet⟩
  have hz : MatrixRestrictions.embed A0 B0
      (0 : MatrixRestrictions.Parameter A0 B0) = 0 :=
    (MatrixRestrictions.embedding A0 B0).map_zero
  have hp (N : MatrixRestrictions.Parameter Z.range Z.ker) :
      mapDerivative Z (hybridDerivative A0 B0 t f) N =
        g (t + RestrictionTransport.nestedEmbedding A0 B0 Z.range Z.ker N) := by
    have hm : (fun Y => Hybrid Y A0 B0 ∧ RankBelow Z (compress Y A0 B0)) =
        a5Mask X A B i := rfl
    have hh := nested_projector_restriction_apply A0 B0 Z.range Z.ker
      (fun Y => Hybrid Y A0 B0) (fun Y => RankBelow Z Y) f t 0 N
    simp only [compressFrequency_eq_compress] at hh
    rw [hm] at hh
    simpa only [mapDerivative, rankProjector, hybridDerivative, hybridProjector,
      g, hz, add_zero] using hh
  calc
    (𝔼 N, mapDerivative Z (hybridDerivative A0 B0 t f) N ^ 2) =
        𝔼 N, g (t + RestrictionTransport.nestedEmbedding A0 B0 Z.range Z.ker N) ^ 2 :=
      Finset.expect_congr rfl fun N _ => congrArg (fun r : ℝ => r ^ 2) (hp N)
    _ = 𝔼 M : MatrixRestrictions.Parameter A B,
        g (t + MatrixRestrictions.embed A B M) ^ 2 := by
      have hrange : (RestrictionTransport.nestedEmbedding A0 B0 Z.range Z.ker).range =
          (MatrixRestrictions.embedding A B).range := by
        rw [RestrictionTransport.nested_range_eq,
          a5_effective_annihilator X A0 A B0 hA hcover,
          a5_effective_codomain X A0 B B0 hdis hmeet]
      have htransport := RestrictionTransport.restriction_secondMoment_eq_of_same_range
        (K := F2) (P := MatrixRestrictions.Parameter Z.range Z.ker)
        (Q := MatrixRestrictions.Parameter A B) (G := E →ₗ[F2] F)
        (RestrictionTransport.nestedEmbedding A0 B0 Z.range Z.ker)
        (MatrixRestrictions.embedding A B)
        (RestrictionTransport.nestedEmbedding_injective A0 B0 Z.range Z.ker)
        (MatrixRestrictions.embed_injective A B) hrange g t
      simpa only [MatrixRestrictions.embedding, LinearMap.coe_mk, AddHom.coe_mk] using htransport

theorem a5_energySquare_le (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F)
    (hI : X.range ≤ A) (hB : B ≤ X.ker)
    [Fintype (A5GeometricIndex X A B)]
    (f : (E →ₗ[F2] F) → ℝ) (S : MatrixRestrictions.Parameter X.range X.ker) :
    (𝔼 N, hybridDerivative (A.map X.range.mkQ) (B.comap X.ker.subtype)
      S (mapDerivative X f) N ^ 2) ^ 2 ≤
    (Fintype.card (A5GeometricIndex X A B) : ℝ) ^ 3 *
      ∑ i : A5GeometricIndex X A B,
        (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
          (hybridDerivative i.val.1 i.val.2
            (MatrixRestrictions.embed X.range X.ker S) f) N ^ 2) ^ 2 := by
  classical
  let J := A5GeometricIndex X A B
  let t := MatrixRestrictions.embed X.range X.ker S
  let g : J → MatrixRestrictions.Parameter A B → ℝ := fun i M =>
    spectralProjector (a5Mask X A B i) f (t + MatrixRestrictions.embed A B M)
  have hp (M : MatrixRestrictions.Parameter A B) :
      spectralProjector (a5OuterMask X A B) f
        (t + MatrixRestrictions.embed A B M) = ∑ i : J, g i M := by
    have h := congrFun (a5_projector_partition X A B hI hB f)
      (t + MatrixRestrictions.embed A B M)
    simpa only [Finset.sum_apply, g] using h
  have ho :
      (𝔼 N, hybridDerivative (A.map X.range.mkQ) (B.comap X.ker.subtype)
        S (mapDerivative X f) N ^ 2) = 𝔼 M, (∑ i : J, g i M) ^ 2 := by
    rw [a5_outer_energy X A B hI hB f S]
    exact Finset.expect_congr rfl fun M _ => congrArg (fun r : ℝ => r ^ 2) (hp M)
  have hi (i : J) :
      (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
        (hybridDerivative i.val.1 i.val.2 t f) N ^ 2) = 𝔼 M, g i M ^ 2 :=
    a5_summand_energy X A B i f S
  rw [ho]
  calc
    (𝔼 M, (∑ i : J, g i M) ^ 2) ^ 2 ≤
        (Fintype.card J : ℝ) ^ 3 * ∑ i : J, (𝔼 M, g i M ^ 2) ^ 2 :=
      energy_sum_sq_le_card_cube g
    _ = (Fintype.card J : ℝ) ^ 3 * ∑ i : J,
        (𝔼 N, mapDerivative (compress X i.val.1 i.val.2)
          (hybridDerivative i.val.1 i.val.2 t f) N ^ 2) ^ 2 := by
      apply congrArg (fun r : ℝ => (Fintype.card J : ℝ) ^ 3 * r)
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun r : ℝ => r ^ 2) (hi i).symm

theorem map_hybrid_fourth_average
    (A0 : Submodule F2 E) (B0 : Submodule F2 F)
    (X : B0 →ₗ[F2] (E ⧸ A0)) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A0 B0 T f) N ^ 4) =
    𝔼 M, spectralProjector
      (fun Y => Hybrid Y A0 B0 ∧ RankBelow X (compress Y A0 B0)) f M ^ 4 := by
  classical
  have hp :
      spectralProjector (fun Y => RankBelow X (Restriction.compressFrequency A0 B0 Y))
        (hybridProjector A0 B0 f) =
      spectralProjector (fun Y => Hybrid Y A0 B0 ∧
        RankBelow X (Restriction.compressFrequency A0 B0 Y)) f := by
    rw [hybridProjector, spectralProjector_comp]
    congr 1
    funext Y
    exact propext and_comm
  have h := Derivatives.spectralProjector_restriction_moment_average A0 B0
    (fun Z => RankBelow X Z) (hybridProjector A0 B0 f)
    (MatrixRestrictions.embed X.range X.ker) 4
  rw [hp] at h
  simpa only [mapDerivative, rankProjector, hybridDerivative,
    MatrixRestrictions.restrict, MatrixRestrictions.translate, zero_add,
    compressFrequency_eq_compress] using h

theorem a4_fourth_average_le (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M ^ 4) ≤
    (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 *
      ∑ i : A4GeometricIndex A B,
        𝔼 T, 𝔼 N, mapDerivative i.val.2.2
          (hybridDerivative i.val.1 i.val.2.1 T f) N ^ 4 := by
  classical
  rw [a4_projector_partition A B f]
  simp only [Finset.sum_apply]
  calc
    (𝔼 M, (∑ i : A4GeometricIndex A B,
        spectralProjector (a4Mask A B i) f M) ^ 4) ≤
      (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 *
        ∑ i : A4GeometricIndex A B, 𝔼 M,
          spectralProjector (a4Mask A B i) f M ^ 4 :=
      average_fourth_sum_le_card_cube
        (fun (i : A4GeometricIndex A B) M => spectralProjector (a4Mask A B i) f M)
    _ = (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 *
        ∑ i : A4GeometricIndex A B,
          𝔼 T, 𝔼 N, mapDerivative i.val.2.2
            (hybridDerivative i.val.1 i.val.2.1 T f) N ^ 4 := by
      apply congrArg (fun r : ℝ =>
        (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 * r)
      apply Finset.sum_congr rfl
      intro i _
      change (𝔼 M, spectralProjector
        (fun Y => Hybrid Y i.val.1 i.val.2.1 ∧
          RankBelow i.val.2.2 (compress Y i.val.1 i.val.2.1)) f M ^ 4) = _
      exact (map_hybrid_fourth_average i.val.1 i.val.2.1 i.val.2.2 f).symm

end UniqueGamesTheorem.Appendix.OperatorNorm

end

end

section

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.OperatorPartitions
open UniqueGamesTheorem.Appendix.LinearIdentities

namespace UniqueGamesTheorem.Appendix.A13Reduction

attribute [local instance] Classical.propDecidable

/-- The exponent comparison after retaining the total degree loss. -/
theorem exponent_le (d i j t : ℕ) (hi : i ≤ t) (hj : j ≤ t) (ht : t ≤ d) :
    7 * d * (i + j) + 3 * i * j ≤ 24 * d * t := by
  have hs : i + j ≤ 2 * t := by omega
  have hp : i * j ≤ d * t :=
    (Nat.mul_le_mul hi hj).trans (Nat.mul_le_mul_right t ht)
  have hfirst := Nat.mul_le_mul_left (7 * d) hs
  have hsecond := Nat.mul_le_mul_left 3 hp
  have hdt : 0 ≤ d * t := Nat.zero_le _
  nlinarith

/-- Degree-forced zero moments allow the same weight bound on every raw triple. -/
theorem weighted_moment_le (d i j t : ℕ) (e : ℝ)
    (hi : i ≤ t) (hj : j ≤ t) (he : 0 ≤ e) (hz : d < t → e = 0) :
    (2 : ℝ) ^ (7 * d * (i + j) + 3 * i * j) * e ≤
      (2 : ℝ) ^ (24 * d * t) * e := by
  by_cases ht : t ≤ d
  · have hn := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2)
      (exponent_le d i j t hi hj ht)
    have hr : (2 : ℝ) ^ (7 * d * (i + j) + 3 * i * j) ≤
        (2 : ℝ) ^ (24 * d * t) := by exact_mod_cast hn
    exact mul_le_mul_of_nonneg_right hr he
  · rw [hz (Nat.lt_of_not_ge ht)]
    simp

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem tripleMoment_nonneg (p : A4Index (K := F2) (W := F) (V := E))
    (f : (E →ₗ[F2] F) → ℝ) : 0 ≤ tripleMoment p f := by
  apply Finset.expect_nonneg
  intro T _
  apply Finset.expect_nonneg
  intro N _
  positivity

/-- A.4's native fourth-moment bound with its proved binary index count. -/
theorem weak_fourth_le_counted (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M ^ 4) ≤
      (2 : ℝ) ^ (3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) *
        ∑ p : A4GeometricIndex A B, tripleMoment p.val f := by
  have hnat := Nat.pow_le_pow_left (A4IndexCount.card_index_le A B) 3
  rw [Nat.card_eq_fintype_card, ← pow_mul] at hnat
  have he : (Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) * 3 =
      3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B) := by ring
  rw [he] at hnat
  have hc : (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 ≤
      (2 : ℝ) ^ (3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) := by
    exact_mod_cast hnat
  have hn : 0 ≤ ∑ p : A4GeometricIndex A B, tripleMoment p.val f :=
    Finset.sum_nonneg fun p _ => tripleMoment_nonneg p.val f
  exact (OperatorNorm.a4_fourth_average_le A B f).trans
    (mul_le_mul_of_nonneg_right hc hn)

/-- Expand one original weak-pair term, retaining its original dimensions. -/
theorem weighted_weak_fourth_le_counted (d : ℕ)
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B))) *
      (𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M ^ 4) ≤
    ∑ p : A4GeometricIndex A B,
      (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B)) +
        3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) * tripleMoment p.val f := by
  calc
    _ ≤ (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B))) *
        ((2 : ℝ) ^ (3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) *
          ∑ p : A4GeometricIndex A B, tripleMoment p.val f) :=
      mul_le_mul_of_nonneg_left (weak_fourth_le_counted A B f) (by positivity)
    _ = _ := by simp only [pow_add, Finset.mul_sum, mul_assoc]

theorem tripleMoment_eq_zero_of_lt_size {d : ℕ}
    (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) (hf : DerivativeDegree.DegreeAtMost d f)
    (h : d < A13Index.size p) : tripleMoment p f = 0 :=
  DerivativeDegree.map_hybridDerivative_fourth_average_eq_zero_of_lt_order_rank
    p.1 p.2.1 p.2.2 f hf h

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem tripleTerm_nonneg (d : ℕ) (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) : 0 ≤ tripleTerm d p f :=
  mul_nonneg (by positivity) (tripleMoment_nonneg p f)

theorem tripleTerm_eq_zero_of_lt_size {d : ℕ}
    (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) (hf : DerivativeDegree.DegreeAtMost d f)
    (h : d < A13Index.size p) : tripleTerm d p f = 0 := by
  unfold tripleTerm
  rw [tripleMoment_eq_zero_of_lt_size p f hf h, mul_zero]

theorem weighted_geometric_moment_le {d : ℕ}
    (A : Submodule F2 E) (B : Submodule F2 F)
    (p : A4GeometricIndex A B) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B)) +
      3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) * tripleMoment p.val f ≤
      tripleTerm d p.val f := by
  have hi : Module.finrank F2 A ≤ A13Index.size p.val := by
    have h := A13Index.dim_weakA p
    unfold A13Index.size MatrixRestrictions.order
    omega
  have hj : Module.finrank F2 (F ⧸ B) ≤ A13Index.size p.val := by
    have h := A13Index.codim_weakB p
    unfold A13Index.size MatrixRestrictions.order
    omega
  exact weighted_moment_le d _ _ _ _ hi hj (tripleMoment_nonneg p.val f)
    (fun h => tripleMoment_eq_zero_of_lt_size p.val f hf h)

variable [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

/-- Apply A.4 and its count, then forget the uniquely reconstructible weak pair.
The old nonzero condition is carried by `positiveMap`; no descendant condition
is substituted for it. -/
theorem weakFourthSum_le_positiveTripleSum (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    A1Reduction.weakFourthSum d f ≤ positiveTripleSum d f := by
  classical
  have heq : A1Reduction.weakFourthSum d f =
      ∑ p : A13Index.WeakPositive (E := E) (F := F),
        (2 : ℝ) ^ (7 * d * (Module.finrank F2 p.val.1 +
          Module.finrank F2 (F ⧸ p.val.2))) *
          (𝔼 M, spectralProjector
            (fun Y => p.val.1 ≤ Y.range ∧ Y.ker ≤ p.val.2) f M ^ 4) := by
    symm
    exact F1Gram.sum_subtype_eq
      (fun p : Submodule F2 E × Submodule F2 F => p ≠ (⊥, ⊤))
      (fun p => (2 : ℝ) ^ (7 * d * (Module.finrank F2 p.1 +
        Module.finrank F2 (F ⧸ p.2))) *
        (𝔼 M, spectralProjector (fun Y => p.1 ≤ Y.range ∧ Y.ker ≤ p.2) f M ^ 4))
  rw [heq]
  calc
    _ ≤ ∑ p : A13Index.WeakPositive (E := E) (F := F),
        ∑ q : A4GeometricIndex p.val.1 p.val.2, tripleTerm d q.val f := by
      apply Finset.sum_le_sum
      intro p _
      exact (weighted_weak_fourth_le_counted d p.val.1 p.val.2 f).trans
        (Finset.sum_le_sum fun q _ => weighted_geometric_moment_le p.val.1 p.val.2 q f hf)
    _ = ∑ w : A13Index.PositiveWitness (E := E) (F := F),
        tripleTerm d w.2.val f := by
      simp only [Fintype.sum_sigma]
    _ ≤ positiveTripleSum d f :=
      F1Gram.sum_comp_le A13Index.positiveMap A13Index.positiveMap_injective
        (fun q : A13Index.PositiveTriple (E := E) (F := F) => tripleTerm d q.val f)
        (fun q => tripleTerm_nonneg d q.val f)

theorem positiveTripleSum_eq_bounded (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    positiveTripleSum d f = boundedPositiveTripleSum d f := by
  classical
  unfold positiveTripleSum boundedPositiveTripleSum
  rw [F1Gram.sum_subtype_eq
      (fun p : A13Index.Triple (E := E) (F := F) => 0 < A13Index.size p)
      (fun p => tripleTerm d p f),
    F1Gram.sum_subtype_eq
      (fun p : A13Index.Triple (E := E) (F := F) =>
        0 < A13Index.size p ∧ A13Index.size p ≤ d)
      (fun p => tripleTerm d p f)]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : 0 < A13Index.size p
  · by_cases ht : A13Index.size p ≤ d
    · rw [ite_eq_left hp, ite_eq_left ⟨hp, ht⟩]
    · rw [ite_eq_left hp, ite_eq_right (fun h => ht h.2)]
      exact tripleTerm_eq_zero_of_lt_size p f hf (Nat.lt_of_not_ge ht)
  · rw [ite_eq_right hp, ite_eq_right (fun h => hp h.1)]

/-- Equation A.13 with the literal positive-triple sum. -/
theorem degree_reduction (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    (𝔼 M, f M ^ 4) / 162 ≤
      (2 : ℝ) ^ (6 * d ^ 2) * (𝔼 M, f M ^ 2) ^ 2 + positiveTripleSum d f := by
  have hbase := A1Reduction.degree_reduction f d (fun Y hY => hf Y hY)
  exact hbase.trans (add_le_add le_rfl (weakFourthSum_le_positiveTripleSum f d hf))

/-- Equation A.13 after removing terms whose actual derivative is zero. -/
theorem degree_reduction_truncated (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    (𝔼 M, f M ^ 4) / 162 ≤
      (2 : ℝ) ^ (6 * d ^ 2) * (𝔼 M, f M ^ 2) ^ 2 + boundedPositiveTripleSum d f := by
  simpa only [positiveTripleSum_eq_bounded f d hf] using degree_reduction f d hf

end UniqueGamesTheorem.Appendix.A13Reduction

end

end

section

/-! Natural changes of domain and codomain preserve rank, Fourier projectors,
and map-derivative energies. The quotient/subtype specialization transports
the actual labels occurring in nested hybrid derivatives. -/

noncomputable section
namespace UniqueGamesTheorem.Appendix.NaturalTransport
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives UniqueGamesTheorem.Appendix.RankAdditivity
attribute [local instance] Classical.propDecidable

section General
variable {E F E' F' : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.NaturalTransport.hybridCompositionQuotientFinite
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.NaturalTransport.hybridCompositionCompressedDualFintype
omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem rank_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F') (L : E →ₗ[F2] F) :
    Module.finrank F2 (LinearEquiv.arrowCongr a b L).range =
      Module.finrank F2 L.range := by
  have hh : LinearEquiv.arrowCongr a b L =
      (b.toLinearMap.comp L).comp a.symm.toLinearMap := by
    ext x
    rfl
  rw [hh, LinearEquiv.range_comp, LinearMap.range_comp]
  exact b.finrank_map_eq L.range

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem rankBelow_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (X Y : F →ₗ[F2] E) :
    RankBelow (LinearEquiv.arrowCongr b a X) (LinearEquiv.arrowCongr b a Y) ↔
      RankBelow X Y := by
  unfold RankBelow
  rw [← map_sub, rank_arrowCongr, rank_arrowCongr, rank_arrowCongr]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem trace_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (M : E →ₗ[F2] F) (Z : F →ₗ[F2] E) :
    linearTracePair (LinearEquiv.arrowCongr a b M) (LinearEquiv.arrowCongr b a Z) =
      linearTracePair M Z := by
  unfold linearTracePair
  rw [← LinearEquiv.arrowCongr_comp]
  exact LinearMap.trace_conj' (M.comp Z) b

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem character_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (M : E →ₗ[F2] F) (Z : F →ₗ[F2] E) :
    linearTraceCharacter (LinearEquiv.arrowCongr b a Z) (LinearEquiv.arrowCongr a b M) =
      linearTraceCharacter Z M := by
  simp only [linearTraceCharacter_apply, trace_arrowCongr]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem admissible_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (Z : F →ₗ[F2] E) (M : E →ₗ[F2] F) :
    ((LinearEquiv.arrowCongr b a Z).range ≤ (LinearEquiv.arrowCongr a b M).ker ∧
      (LinearEquiv.arrowCongr a b M).range ≤ (LinearEquiv.arrowCongr b a Z).ker) ↔
    (Z.range ≤ M.ker ∧ M.range ≤ Z.ker) := by
  simp [LinearMap.range_le_ker_iff, ← LinearEquiv.arrowCongr_comp]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem derivative_embedding_range (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (Z : F →ₗ[F2] E) :
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding Z.range Z.ker)).range =
      (embedding (LinearEquiv.arrowCongr b a Z).range
        (LinearEquiv.arrowCongr b a Z).ker).range := by
  let e : (E →ₗ[F2] F) ≃ₗ[F2] (E' →ₗ[F2] F') := LinearEquiv.arrowCongr a b
  let Z' := LinearEquiv.arrowCongr b a Z
  ext M'
  change (∃ N, e (embed Z.range Z.ker N) = M') ↔
    (∃ N, embed Z'.range Z'.ker N = M')
  constructor
  · rintro ⟨N, rfl⟩
    apply (exists_embed_iff Z'.range Z'.ker _).mpr
    apply (admissible_arrowCongr a b Z (embed Z.range Z.ker N)).mpr
    exact (exists_embed_iff Z.range Z.ker _).mp ⟨N, rfl⟩
  · intro hM'
    let M := e.symm M'
    have he : e M = M' := e.apply_symm_apply M'
    have hm' := (exists_embed_iff Z'.range Z'.ker M').mp hM'
    have hm : Z.range ≤ M.ker ∧ M.range ≤ Z.ker := by
      apply (admissible_arrowCongr a b Z M).mp
      change Z'.range ≤ (e M).ker ∧ (e M).range ≤ Z'.ker
      rw [he]
      exact hm'
    obtain ⟨N, hN⟩ := (exists_embed_iff Z.range Z.ker M).mpr hm
    refine ⟨N, ?_⟩
    rw [hN]
    exact he

variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E' →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E')]

omit [Fintype (F →ₗ[F2] E)] [Fintype (F' →ₗ[F2] E')]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F'] in
theorem linearCoeff_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (Z : F →ₗ[F2] E) :
    linearCoeff (fun M => f (LinearEquiv.arrowCongr a b M)) Z =
      linearCoeff f (LinearEquiv.arrowCongr b a Z) := by
  unfold linearCoeff
  exact Fintype.expect_equiv (LinearEquiv.arrowCongr a b).toEquiv _ _
    (fun M => by
      change f (LinearEquiv.arrowCongr a b M) * (linearTraceCharacter Z M).re =
        f (LinearEquiv.arrowCongr a b M) *
          (linearTraceCharacter (LinearEquiv.arrowCongr b a Z)
            (LinearEquiv.arrowCongr a b M)).re
      rw [character_arrowCongr])

theorem rankProjector_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (Z : F →ₗ[F2] E) :
    rankProjector Z (fun M => f (LinearEquiv.arrowCongr a b M)) =
      fun M => rankProjector (LinearEquiv.arrowCongr b a Z) f
        (LinearEquiv.arrowCongr a b M) := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [rankProjector, linearCoeff_spectralProjector,
    linearCoeff_pullback, rankBelow_arrowCongr]

variable [Finite E] [Finite F] [Finite E'] [Finite F']

theorem mapDerivative_energy_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (Z : F →ₗ[F2] E) :
    (𝔼 N, mapDerivative Z (fun M => f (LinearEquiv.arrowCongr a b M)) N ^ 2) =
      𝔼 N, mapDerivative (LinearEquiv.arrowCongr b a Z) f N ^ 2 := by
  simp only [mapDerivative, restrict,
    UniqueGamesTheorem.Fourier.MatrixRestrictions.translate, zero_add]
  rw [rankProjector_pullback]
  exact RestrictionTransport.expect_eq_of_same_range
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding Z.range Z.ker))
    (embedding (LinearEquiv.arrowCongr b a Z).range (LinearEquiv.arrowCongr b a Z).ker)
    ((LinearEquiv.arrowCongr a b).injective.comp (embed_injective Z.range Z.ker))
    (embed_injective _ _) (derivative_embedding_range a b Z)
    (fun M => rankProjector (LinearEquiv.arrowCongr b a Z) f M ^ 2)

end General

section Nested
variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.NaturalTransport.hybridCompositionQuotientFinite
attribute [local instance] OAI.UniqueGamesTheorem.Appendix.NaturalTransport.hybridCompositionCompressedDualFintype
omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem dualFactor_rank (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (Z : D →ₗ[F2] ((E ⧸ A) ⧸ C)) :
    Module.finrank F2 (dualFactor A B C D Z).range = Module.finrank F2 Z.range :=
  rank_arrowCongr (outputFactor B D) (quotientFactor A C).symm Z

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem parameterFactor_embedding (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) (N : Parameter C D) :
    embed (C.comap A.mkQ) (D.map B.subtype) (parameterFactor A B C D N) =
      RestrictionTransport.nestedEmbedding A B C D N := by
  ext x
  change ((outputFactor B D (N (quotientFactor A C ((C.comap A.mkQ).mkQ x)))) : F) =
    ((N (C.mkQ (A.mkQ x)) : B) : F)
  rw [quotientFactor_mkQ]
  rfl

theorem nested_hybridDerivative_function
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) (S : Parameter A B) :
    hybridDerivative C D S (hybridDerivative A B T f) =
      fun N => hybridDerivative (C.comap A.mkQ) (D.map B.subtype)
        (T + embed A B S) f (parameterFactor A B C D N) := by
  funext N
  have hh := OperatorNorm.nested_projector_restriction_apply A B C D
    (fun Y => LinearIdentities.Hybrid Y A B)
    (fun Z => LinearIdentities.Hybrid Z C D) f T S N
  have hp : (fun Y => LinearIdentities.Hybrid Y A B ∧
        LinearIdentities.Hybrid (Restriction.compressFrequency A B Y) C D) =
      (fun Y => LinearIdentities.Hybrid Y (C.comap A.mkQ) (D.map B.subtype)) := by
    funext Y
    exact propext (HybridComposition.effective_hybrid_iff A B C D Y)
  rw [hp] at hh
  change _ = hybridProjector (C.comap A.mkQ) (D.map B.subtype) f
    ((T + embed A B S) + embed (C.comap A.mkQ) (D.map B.subtype)
      (parameterFactor A B C D N))
  rw [parameterFactor_embedding]
  exact hh

theorem nested_mapDerivative_energy
    (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B)
    (f : (E →ₗ[F2] F) → ℝ) (T : E →ₗ[F2] F) (S : Parameter A B)
    (Z : D →ₗ[F2] ((E ⧸ A) ⧸ C)) :
    (𝔼 N, mapDerivative Z (hybridDerivative C D S (hybridDerivative A B T f)) N ^ 2) =
      𝔼 N, mapDerivative (dualFactor A B C D Z)
        (hybridDerivative (C.comap A.mkQ) (D.map B.subtype) (T + embed A B S) f) N ^ 2 := by
  rw [nested_hybridDerivative_function]
  exact mapDerivative_energy_pullback (quotientFactor A C).symm (outputFactor B D)
    (hybridDerivative (C.comap A.mkQ) (D.map B.subtype) (T + embed A B S) f) Z

end Nested
end UniqueGamesTheorem.Appendix.NaturalTransport

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_A5FrequencyTransportLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem

/-! Pointwise identification of the natural frequency transport with the
relative frequency used by the actual reverse compression fibers. -/

/-! Canonical indices for the Appendix A.5 induction passage. The outer
hybrid index is recovered from its actual geometric pair, so forgetting it
does not increase multiplicity. -/

namespace Appendix.A5Passage

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.Derivatives
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

theorem comap_mkQ_injective (P : Submodule F2 E) :
    Function.Injective (fun A : Submodule F2 (E ⧸ P) => A.comap P.mkQ) := by
  intro A B h
  change A.comap P.mkQ = B.comap P.mkQ at h
  ext z
  obtain ⟨v, rfl⟩ := P.mkQ_surjective z
  change v ∈ A.comap P.mkQ ↔ v ∈ B.comap P.mkQ
  rw [h]

theorem map_subtype_injective (P : Submodule F2 E) :
    Function.Injective (fun A : Submodule F2 P => A.map P.subtype) := by
  intro A B h
  change A.map P.subtype = B.map P.subtype at h
  ext z
  constructor
  · intro hz
    have hm : (z : E) ∈ A.map P.subtype :=
      Submodule.mem_map.mpr ⟨z, hz, rfl⟩
    rw [h] at hm
    rcases Submodule.mem_map.mp hm with ⟨v, hv, he⟩
    have hvz : v = z := Subtype.ext he
    simpa only [hvz] using hv
  · intro hz
    have hm : (z : E) ∈ B.map P.subtype :=
      Submodule.mem_map.mpr ⟨z, hz, rfl⟩
    rw [← h] at hm
    rcases Submodule.mem_map.mp hm with ⟨v, hv, he⟩
    have hvz : v = z := Subtype.ext he
    simpa only [hvz] using hv

theorem outer_eq_of_lifted (X : F →ₗ[F2] E) {e : Nat} (s t : OuterIndex X e)
    (hA : LiftedA X s = LiftedA X t) (hB : LiftedB X s = LiftedB X t) : s = t := by
  apply Subtype.ext
  exact Prod.ext (comap_mkQ_injective X.range hA) (map_subtype_injective X.ker hB)

theorem forget_injective (X : F →ₗ[F2] E) (e : Nat) :
    Function.Injective (forget X e) := by
  rintro ⟨s, p⟩ ⟨t, q⟩ h
  change p.val = q.val at h
  have hA : LiftedA X s = LiftedA X t := by
    calc
      LiftedA X s = p.val.1 ⊔ X.range := p.property.2.1.symm
      _ = q.val.1 ⊔ X.range := congrArg (fun A => A ⊔ X.range) (congrArg Prod.fst h)
      _ = LiftedA X t := q.property.2.1
  have hB : LiftedB X s = LiftedB X t := by
    calc
      LiftedB X s = p.val.2 ⊓ X.ker := p.property.2.2.2.symm
      _ = q.val.2 ⊓ X.ker := congrArg (fun B => B ⊓ X.ker) (congrArg Prod.snd h)
      _ = LiftedB X t := q.property.2.2.2
  have hst := outer_eq_of_lifted X s t hA hB
  cases hst
  have hpq : p = q := Subtype.ext h
  cases hpq
  rfl

variable [Finite E] [Finite F]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem dim_pairA (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    Module.finrank F2 q.2.val.1 = Module.finrank F2 q.1.val.1 := by
  have hsup := q.2.val.1.finrank_sup_add_finrank_inf_eq X.range
  rw [q.2.property.2.1, q.2.property.1.eq_bot, finrank_bot, add_zero] at hsup
  have hcomap := HybridComposition.finrank_comap_mkQ X.range q.1.val.1
  change Module.finrank F2 (LiftedA X q.1) =
    Module.finrank F2 X.range + Module.finrank F2 q.1.val.1 at hcomap
  omega

omit [Finite E] [Finite F] [FiniteDimensional F2 E]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem codim_pairB (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    Module.finrank F2 (F ⧸ q.2.val.2) =
      Module.finrank F2 (X.ker ⧸ q.1.val.2) := by
  have hsup := q.2.val.2.finrank_sup_add_finrank_inf_eq X.ker
  rw [q.2.property.2.2.1, q.2.property.2.2.2, finrank_top] at hsup
  have hmap := Submodule.finrank_map_subtype_eq X.ker q.1.val.2
  change Module.finrank F2 (LiftedB X q.1) = Module.finrank F2 q.1.val.2 at hmap
  have hF := q.2.val.2.finrank_quotient_add_finrank
  have hK := q.1.val.2.finrank_quotient_add_finrank
  change Module.finrank F2 (X.ker ⧸ q.1.val.2) + Module.finrank F2 q.1.val.2 =
    Module.finrank F2 X.ker at hK
  omega

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem pair_order (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    UniqueGamesTheorem.Fourier.MatrixRestrictions.order q.2.val.1 q.2.val.2 =
      UniqueGamesTheorem.Fourier.MatrixRestrictions.order q.1.val.1 q.1.val.2 := by
  unfold UniqueGamesTheorem.Fourier.MatrixRestrictions.order
  rw [dim_pairA X q, codim_pairB X q]

omit [Finite E] [Finite F] [FiniteDimensional F2 E]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem pair_rank (X : F →ₗ[F2] E) {e : Nat} (q : Passage X e) :
    Module.finrank F2 (LinearIdentities.compress X q.2.val.1 q.2.val.2).range =
      Module.finrank F2 X.range :=
  LinearIdentities.compress_rank_preserved X q.2.val.1 q.2.val.2
    q.2.property.1 q.2.property.2.2.1

omit [Finite E] [Finite F] [FiniteDimensional F2 E]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem descendant_rank (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) {e : Nat} (q : Passage X e) :
    Module.finrank F2 (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
      (LinearIdentities.compress X q.2.val.1 q.2.val.2)).range =
      Module.finrank F2 X.range := by
  rw [NaturalTransport.dualFactor_rank]
  exact pair_rank X q

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem effective_order_rank (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) {e : Nat} (q : Passage X e) :
    UniqueGamesTheorem.Fourier.MatrixRestrictions.order
        (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) +
      Module.finrank F2 (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2)).range =
      UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B +
        UniqueGamesTheorem.Fourier.MatrixRestrictions.order q.1.val.1 q.1.val.2 +
        Module.finrank F2 X.range := by
  rw [HybridComposition.order_effective, NaturalTransport.dualFactor_rank,
    pair_order, pair_rank]

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem effective_order_rank_le (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (d : Nat)
    (h : UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B + Module.finrank F2 X.range ≤ d)
    (q : Passage X (d - (UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B +
      Module.finrank F2 X.range))) :
    UniqueGamesTheorem.Fourier.MatrixRestrictions.order
        (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) +
      Module.finrank F2 (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2)).range ≤ d := by
  rw [effective_order_rank]
  have hq := q.1.property
  change UniqueGamesTheorem.Fourier.MatrixRestrictions.order q.1.val.1 q.1.val.2 ≤
    d - (UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B + Module.finrank F2 X.range) at hq
  omega

end Appendix.A5Passage

namespace Appendix.A5ForwardIndex

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions (order)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem descendant_rank {d : ℕ} (a : Index (E := E) (F := F) d) :
    targetRank (descendant a) = Module.finrank F2 a.1.val.2.2.range :=
  A5Passage.descendant_rank a.1.val.1 a.1.val.2.1 a.1.val.2.2 a.2

omit [FiniteDimensional F2 E] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem original_size {d : ℕ} (a : Index (E := E) (F := F) d) :
    sourceI a + sourceJ a + targetRank (descendant a) = A13Index.size a.1.val := by
  rw [descendant_rank]
  rfl

omit [FiniteDimensional F2 E] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem original_order_bounds {d : ℕ} (a : Index (E := E) (F := F) d) :
    1 ≤ sourceI a + sourceJ a + targetRank (descendant a) ∧
      sourceI a + sourceJ a + targetRank (descendant a) ≤ d := by
  rw [original_size]
  exact a.1.property

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem descendant_size_le {d : ℕ} (a : Index (E := E) (F := F) d) :
    A13Index.size (descendant a) ≤ d :=
  A5Passage.effective_order_rank_le a.1.val.1 a.1.val.2.1 a.1.val.2.2 d
    a.1.property.2 a.2

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem earlierTriple_encode (d : ℕ)
    (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) (a : Fiber d r i j) :
    earlierTriple (encode d r i j a) = a.val.1.val := by
  rcases a with ⟨a, hr, hi, hj⟩
  cases hr
  rfl

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- Fixing the result and retained earlier data fixes both the complementary
pair and its outer hybrid index. No additional outer-index factor occurs. -/
theorem encode_injective (d : ℕ)
    (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) :
    Function.Injective (encode d r i j) := by
  intro a b hab
  have hraw : a.val.1.val = b.val.1.val := by
    simpa only [earlierTriple_encode] using congrArg earlierTriple hab
  have hbase : a.val.1 = b.val.1 := Subtype.ext hraw
  have hresult : descendant a.val = descendant b.val := a.property.1.trans b.property.1.symm
  rcases a with ⟨⟨r₁, p⟩, ha⟩
  rcases b with ⟨⟨r₂, q⟩, hb⟩
  change r₁ = r₂ at hbase
  cases hbase
  have hA := congrArg (fun z : A13Index.Triple (E := E) (F := F) => z.1) hresult
  have hB := congrArg (fun z : A13Index.Triple (E := E) (F := F) => z.2.1) hresult
  change p.2.val.1.comap r₁.val.1.mkQ = q.2.val.1.comap r₁.val.1.mkQ at hA
  change p.2.val.2.map r₁.val.2.1.subtype = q.2.val.2.map r₁.val.2.1.subtype at hB
  have hpq : p = q := A5Passage.forget_injective r₁.val.2.2 _
    (Prod.ext (A5Passage.comap_mkQ_injective r₁.val.1 hA)
      (A5Passage.map_subtype_injective r₁.val.2.1 hB))
  cases hpq
  rfl

variable [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

attribute [local instance] OAI.UniqueGamesTheorem.Appendix.A5ForwardIndex.indexFintype
omit [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- Actual cardinality bound for every fiber used by the weighted reversal. -/
theorem card_fiber_le (d : ℕ) (r : A13Index.Triple (E := E) (F := F)) (i j : ℕ) :
    Nat.card (Fiber d r i j) ≤ 2 ^ (3 * (d * (i + j + targetRank r))) := by
  by_cases hn : Nonempty (Fiber d r i j)
  · obtain ⟨a⟩ := hn
    have hsize : A13Index.size r ≤ d := by
      rw [← a.property.1]
      exact descendant_size_le a.val
    have hA : Module.finrank F2 r.1 ≤ d := by
      unfold A13Index.size order at hsize
      omega
    have hB : Module.finrank F2 (F ⧸ r.2.1) ≤ d := by
      unfold A13Index.size order at hsize
      omega
    have ht : i + j + targetRank r ≤ d := by
      have h := (original_order_bounds a.val).2
      rwa [a.property.1, a.property.2.1, a.property.2.2] at h
    have hcount := A5ReverseIndex.card_ancestor_le_source r.1 r.2.1 r.2.2
      d i j (targetRank r) (le_refl _) hA hB ht
    exact (Nat.card_le_card_of_injective (encode d r i j)
      (encode_injective d r i j)).trans hcount
  · have : IsEmpty (Fiber d r i j) := ⟨fun a => hn ⟨a⟩⟩
    simp

end Appendix.A5ForwardIndex

/-!
# The actual weighted reversal in Appendix A.5

The forward index records an original positive triple and an actual A.5
passage. Its checked reverse-fiber bound permits finite weighted grouping.
The resulting weights are the moments of the actual transported derivatives.
No degree hypothesis or analytic induction hypothesis is used here.
-/

namespace Appendix.A5ReverseSum

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions (order)
open Derivatives
open A5ForwardIndex

attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype
attribute [local instance] SubspaceExtensions.subspaceFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem targetWeight_nonneg (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (r : A13Index.Triple (E := E) (F := F)) : 0 ≤ targetWeight d f r := by
  unfold targetWeight
  split_ifs
  · exact Finset.expect_nonneg fun _ _ => sq_nonneg _
  · exact le_refl _

theorem targetWeight_descendant (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (a : Index (E := E) (F := F) d) :
    targetWeight d f (descendant a) = actualMoment f (descendant a) := by
  have h := descendant_size_le a
  have ho : order (descendant a).1 (descendant a).2.1 ≤ d := by
    unfold A13Index.size at h
    omega
  exact ite_eq_left ho

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- The target cutoff is exactly the actual finite hybrid index. -/
theorem sum_triples_cutoff (d : ℕ)
    (H : ∀ (A : Submodule F2 E) (B : Submodule F2 F),
      (B →ₗ[F2] (E ⧸ A)) → ℝ) :
    (∑ r : A13Index.Triple (E := E) (F := F),
      if order r.1 r.2.1 ≤ d then H r.1 r.2.1 r.2.2 else 0) =
    ∑ s : HybridIndex (E := E) (F := F) d,
      ∑ Y : s.val.2 →ₗ[F2] (E ⧸ s.val.1), H s.val.1 s.val.2 Y := by
  classical
  let G : Submodule F2 E × Submodule F2 F → ℝ :=
    fun p => ∑ Y : p.2 →ₗ[F2] (E ⧸ p.1), H p.1 p.2 Y
  have hh : (∑ s : HybridIndex (E := E) (F := F) d, G s.val) =
      ∑ p : Submodule F2 E × Submodule F2 F,
        if order p.1 p.2 ≤ d then G p else 0 := by
    calc
      _ = ∑ p ∈ Finset.univ.filter (fun p : Submodule F2 E × Submodule F2 F =>
            order p.1 p.2 ≤ d), G p := by
        exact (Finset.sum_subtype _ (by simp) G).symm
      _ = _ := Finset.sum_filter _ _
  change _ = ∑ s : HybridIndex (E := E) (F := F) d, G s.val
  rw [hh, Fintype.sum_prod_type]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro A _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro B _
  by_cases h : order A B ≤ d
  · simp only [h, ite_true, if_true, G]
  · simp only [h, ite_false, Finset.sum_const_zero]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem target_sum_eq (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (∑ r : A13Index.Triple (E := E) (F := F),
      ((2 : ℝ)⁻¹) ^ (31 * d * (targetRank r + 1) + 4 * d * targetRank r) *
        targetWeight d f r) =
    ∑ s : HybridIndex (E := E) (F := F) d,
      𝔼 T, ∑ Y : s.val.2 →ₗ[F2] (E ⧸ s.val.1),
        ((2 : ℝ)⁻¹) ^ (31 * d * (Module.finrank F2 Y.range + 1) +
          4 * d * Module.finrank F2 Y.range) *
          (𝔼 N, mapDerivative Y (hybridDerivative s.val.1 s.val.2 T f) N ^ 2) ^ 2 := by
  let H : ∀ (A : Submodule F2 E) (B : Submodule F2 F),
      (B →ₗ[F2] (E ⧸ A)) → ℝ := fun A B Y =>
    ((2 : ℝ)⁻¹) ^ (31 * d * (Module.finrank F2 Y.range + 1) +
      4 * d * Module.finrank F2 Y.range) * actualMoment f ⟨A, B, Y⟩
  calc
    _ = ∑ r : A13Index.Triple (E := E) (F := F),
        if order r.1 r.2.1 ≤ d then H r.1 r.2.1 r.2.2 else 0 := by
      apply Finset.sum_congr rfl
      rintro ⟨A, B, Y⟩ _
      simp only [targetWeight, targetRank, H, mul_ite, mul_zero]
    _ = ∑ s : HybridIndex (E := E) (F := F) d,
        ∑ Y : s.val.2 →ₗ[F2] (E ⧸ s.val.1), H s.val.1 s.val.2 Y :=
      sum_triples_cutoff d H
    _ = _ := ?_
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro Y _
  rw [← Finset.mul_expect]
  rfl

theorem source_summand_eq (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (a : Index (E := E) (F := F) d) :
    (2 : ℝ) ^ (100 * (d - (sourceI a + sourceJ a + targetRank (descendant a))) ^ 2 +
      24 * d * (sourceI a + sourceJ a + targetRank (descendant a)) +
      6 * d * targetRank (descendant a)) * targetWeight d f (descendant a) =
    (2 : ℝ) ^ (100 * (d - A13Index.size a.1.val) ^ 2 +
      24 * d * A13Index.size a.1.val + 6 * d * Module.finrank F2 a.1.val.2.2.range) *
        actualMoment f (descendant a) := by
  rw [original_size, descendant_rank, targetWeight_descendant]

theorem source_sum_eq (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (∑ a : Index (E := E) (F := F) d,
      (2 : ℝ) ^ (100 * (d - (sourceI a + sourceJ a + targetRank (descendant a))) ^ 2 +
        24 * d * (sourceI a + sourceJ a + targetRank (descendant a)) +
        6 * d * targetRank (descendant a)) * targetWeight d f (descendant a)) =
    ∑ r : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
      (2 : ℝ) ^ (100 * (d - A13Index.size r.val) ^ 2 + 24 * d * A13Index.size r.val +
        6 * d * Module.finrank F2 r.val.2.2.range) *
        A5Passage.descendantSum r.val.1 r.val.2.1 r.val.2.2
          (d - A13Index.size r.val) f := by
  simp_rw [source_summand_eq]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _
  rw [A5Passage.descendantSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rfl

/-- The weighted sum of actual A.5 descendants is bounded by damped actual
map-derivative moments over all hybrid restrictions of order at most `d`. -/
theorem weighted_descendantSum_le (d : ℕ) (hd : 1 ≤ d)
    (f : (E →ₗ[F2] F) → ℝ) :
    (∑ r : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
      (2 : ℝ) ^ (100 * (d - A13Index.size r.val) ^ 2 + 24 * d * A13Index.size r.val +
        6 * d * Module.finrank F2 r.val.2.2.range) *
        A5Passage.descendantSum r.val.1 r.val.2.1 r.val.2.2
          (d - A13Index.size r.val) f) ≤
    (2 : ℝ) ^ (100 * d * d) *
      ∑ s : HybridIndex (E := E) (F := F) d,
        𝔼 T, ∑ Y : s.val.2 →ₗ[F2] (E ⧸ s.val.1),
          ((2 : ℝ)⁻¹) ^ (31 * d * (Module.finrank F2 Y.range + 1) +
            4 * d * Module.finrank F2 Y.range) *
            (𝔼 N, mapDerivative Y (hybridDerivative s.val.1 s.val.2 T f) N ^ 2) ^ 2 := by
  have h := A5WeightedReindex.weighted_reindex d hd
    (descendant (E := E) (F := F) (d := d)) sourceI sourceJ targetRank
    (targetWeight d f) (targetWeight_nonneg d f) original_order_bounds
    (fun r i j => by simpa only [Nat.mul_assoc] using card_fiber_le d r i j)
  rwa [source_sum_eq, target_sum_eq] at h

end Appendix.A5ReverseSum

/-! Actual norm and induction steps for Proposition A.5. The universal degree
property below is the motive for strong induction on the degree; defining
that property does not assert its truth. -/

namespace Appendix.A5Induction

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives UniqueGamesTheorem.Appendix.DerivativeDegree
open UniqueGamesTheorem.Appendix.LevelInequality (frequencyRank)
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype
attribute [local instance] SubspaceExtensions.subspaceFintype

universe u v

theorem damping_le (d k : ℕ) :
    (1 / 2 : ℝ) ^ (31 * d * (k + 1) + 4 * d * k) ≤
      (1 / 2 : ℝ) ^ (31 * d) * (1 / 2 : ℝ) ^ (8 * d * k) := by
  have hpow (n : ℕ) : (1 / 2 : ℝ) ^ n ≤ 1 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      have hn := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n
      nlinarith
  have he : 31 * d * (k + 1) + 4 * d * k =
      (31 * d + 8 * d * k) + 27 * d * k := by ring
  rw [he, pow_add, pow_add]
  have hh := mul_le_mul_of_nonneg_left (hpow (27 * d * k))
    (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (31 * d))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (8 * d * k)))
  simpa only [mul_one] using hh

theorem coefficient_absorption (d : ℕ) (hd : 1 ≤ d) :
    (162 : ℝ) * ((2 : ℝ) ^ (6 * d * d) +
      (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d))) ≤
      (2 : ℝ) ^ (100 * d * d) := by
  have hfirst : (2 : ℝ) ^ (100 * d * d) *
      ((2 : ℝ) ^ (94 * d * d))⁻¹ = (2 : ℝ) ^ (6 * d * d) := by
    have he : 100 * d * d = 6 * d * d + 94 * d * d := by ring
    rw [he, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)),
      mul_one]
  have he : 31 * d = (31 * d - 1) + 1 := by omega
  have hsecond : ((2 : ℝ) ^ (31 * d - 1))⁻¹ =
      2 * (1 / 2 : ℝ) ^ (31 * d) := by
    calc
      ((2 : ℝ) ^ (31 * d - 1))⁻¹ = (1 / 2 : ℝ) ^ (31 * d - 1) := by
        rw [one_div, inv_pow]
      _ = 2 * ((1 / 2 : ℝ) ^ (31 * d - 1) * (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [← pow_succ, ← he]
  have hscaled := mul_le_mul_of_nonneg_right (A5Scalar.absorption hd)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (100 * d * d))
  calc
    (162 : ℝ) * ((2 : ℝ) ^ (6 * d * d) +
        (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d))) =
        162 * (((2 : ℝ) ^ (94 * d * d))⁻¹ +
          ((2 : ℝ) ^ (31 * d - 1))⁻¹) * (2 : ℝ) ^ (100 * d * d) := by
      symm
      calc
        _ = 162 * ((2 : ℝ) ^ (100 * d * d) * ((2 : ℝ) ^ (94 * d * d))⁻¹ +
            (2 : ℝ) ^ (100 * d * d) * ((2 : ℝ) ^ (31 * d - 1))⁻¹) := by ring
        _ = _ := by rw [hfirst, hsecond]
    _ ≤ _ := by simpa only [one_mul] using hscaled

variable {E : Type u} {F : Type v}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Finite E] [Finite F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem dampedMapMoment_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    dampedMapMoment d f ≤
      (2 * (1 / 2 : ℝ) ^ (31 * d)) * (𝔼 M, f M ^ 2) ^ 2 := by
  have hterms : dampedMapMoment d f ≤ (1 / 2 : ℝ) ^ (31 * d) *
      ∑ X : F →ₗ[F2] E, (1 / 2 : ℝ) ^ (8 * d * frequencyRank X) *
        (𝔼 N, mapDerivative X f N ^ 2) ^ 2 := by
    unfold dampedMapMoment
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro X _
    have hh := mul_le_mul_of_nonneg_right (damping_le d (frequencyRank X))
      (sq_nonneg (𝔼 N, mapDerivative X f N ^ 2))
    simpa only [mul_assoc] using hh
  have hbase := weighted_fourth_derivative_energy f d (fun Y hY => hf Y hY)
  have hbase' :
      (∑ X : F →ₗ[F2] E, (1 / 2 : ℝ) ^ (8 * d * frequencyRank X) *
        (𝔼 N, mapDerivative X f N ^ 2)^2) ≤ 2 * (𝔼 M, f M ^ 2)^2 := by
    simpa only [one_div, frequencyRank] using hbase
  calc
    dampedMapMoment d f ≤ _ := hterms
    _ ≤ (1 / 2 : ℝ) ^ (31 * d) * (2 * (𝔼 M, f M ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hbase'
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _)
    _ = _ := by ring

theorem dampedHybridMoment_le (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    dampedHybridMoment d f ≤
      (2 * (1 / 2 : ℝ) ^ (31 * d)) * hybridMomentSum d f := by
  unfold dampedHybridMoment hybridMomentSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  calc
    (𝔼 T, dampedMapMoment d (hybridDerivative s.val.1 s.val.2 T f)) ≤
        𝔼 T, (2 * (1 / 2 : ℝ) ^ (31 * d)) *
          (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2) ^ 2 := by
      apply Finset.expect_le_expect
      intro T _
      exact dampedMapMoment_le d _
        ((degree_hybridDerivative s.val.1 s.val.2 T f hf).mono (Nat.sub_le _ _))
    _ = _ := by rw [← Finset.mul_expect]

omit [Finite E] [Finite F] in
theorem hybridProjector_zero_pair (f : (E →ₗ[F2] F) → ℝ) :
    hybridProjector (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) f = f := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp [hybridProjector, linearCoeff_spectralProjector, LinearIdentities.Hybrid]

theorem energy_sq_le_hybridMomentSum (d : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 M, f M ^ 2) ^ 2 ≤ hybridMomentSum d f := by
  have hzero : Module.finrank F2 (F ⧸ (⊤ : Submodule F2 F)) = 0 := by
    have hq := (⊤ : Submodule F2 F).finrank_quotient_add_finrank
    have he : Module.finrank F2 (F ⧸ (⊤ : Submodule F2 F)) + Module.finrank F2 F =
        Module.finrank F2 F := by simpa using hq
    omega
  let s0 : HybridIndex (E := E) (F := F) d := ⟨(⊥, ⊤), by
    change Module.finrank F2 (⊥ : Submodule F2 E) +
      Module.finrank F2 (F ⧸ (⊤ : Submodule F2 F)) ≤ d
    rw [hzero]
    simp⟩
  have havg := hybridDerivative_energy_average
    (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) f
  rw [hybridProjector_zero_pair] at havg
  have hcs : (𝔼 T, 𝔼 N,
      hybridDerivative (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) T f N ^ 2) ^ 2 ≤
      𝔼 T, (𝔼 N,
        hybridDerivative (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) T f N ^ 2) ^ 2 := by
    simpa using Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
      (fun T => 𝔼 N,
        hybridDerivative (⊥ : Submodule F2 E) (⊤ : Submodule F2 F) T f N ^ 2)
      (fun _ => (1 : ℝ))
  rw [havg] at hcs
  apply hcs.trans
  change (𝔼 T, (𝔼 N, hybridDerivative s0.val.1 s0.val.2 T f N ^ 2) ^ 2) ≤ _
  unfold hybridMomentSum
  let H : HybridIndex (E := E) (F := F) d → ℝ :=
    fun s => 𝔼 T, (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2)^2
  change H s0 ≤ ∑ s, H s
  exact Finset.single_le_sum (f := H) (s := Finset.univ)
    (fun s _ => Finset.expect_nonneg (fun T _ =>
      sq_nonneg (𝔼 N, hybridDerivative s.val.1 s.val.2 T f N ^ 2)))
    (Finset.mem_univ s0)

theorem degree_zero_bound (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost 0 f) :
    (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * 0 * 0) * hybridMomentSum 0 f := by
  rw [DegreeZero.fourth_moment_eq_energy_sq f (fun Y hY => hf Y hY)]
  simpa using energy_sq_le_hybridMomentSum 0 f

/-- Close the actual recurrence once its finite index expansion is supplied.
This lemma states that recurrence explicitly; it is not the public A.5 theorem. -/
theorem recurrence_closure (d : ℕ) (hd : 1 ≤ d)
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f)
    (hrec : (𝔼 M, f M ^ 4) / 162 ≤
      (2 : ℝ) ^ (6 * d * d) * (𝔼 M, f M ^ 2)^2 +
        (2 : ℝ) ^ (100 * d * d) * dampedHybridMoment d f) :
    (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * d * d) * hybridMomentSum d f := by
  have hS : 0 ≤ hybridMomentSum d f :=
    Finset.sum_nonneg (fun s _ => Finset.expect_nonneg (fun T _ => sq_nonneg _))
  have herror := mul_le_mul_of_nonneg_left (energy_sq_le_hybridMomentSum d f)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (6 * d * d))
  have hdamp := mul_le_mul_of_nonneg_left (dampedHybridMoment_le d f hf)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (100 * d * d))
  have hrec' : (𝔼 M, f M ^ 4) / 162 ≤
      ((2 : ℝ) ^ (6 * d * d) +
        (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d))) *
          hybridMomentSum d f := by
    calc
      _ ≤ _ := hrec
      _ ≤ (2 : ℝ) ^ (6 * d * d) * hybridMomentSum d f +
          (2 : ℝ) ^ (100 * d * d) *
            ((2 * (1 / 2 : ℝ) ^ (31 * d)) * hybridMomentSum d f) :=
        add_le_add herror hdamp
      _ = _ := by ring
  calc
    (𝔼 M, f M ^ 4) = 162 * ((𝔼 M, f M ^ 4) / 162) := by ring
    _ ≤ 162 * (((2 : ℝ) ^ (6 * d * d) +
        (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d))) *
          hybridMomentSum d f) := mul_le_mul_of_nonneg_left hrec' (by norm_num)
    _ = (162 * ((2 : ℝ) ^ (6 * d * d) +
        (2 : ℝ) ^ (100 * d * d) * (2 * (1 / 2 : ℝ) ^ (31 * d)))) *
          hybridMomentSum d f := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (coefficient_absorption d hd) hS

omit [Finite E] [Finite F] [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- Dimension bounds for the outer subspaces used by the actual A.5 operator
identity, obtained from the order of an actual derivative-space index. -/
theorem lifted_outer_dimensions (X : F →ₗ[F2] E)
    (C : Submodule F2 (E ⧸ X.range)) (D : Submodule F2 X.ker)
    (d : ℕ) (hcut : Module.finrank F2 X.range + order C D ≤ d) :
    Module.finrank F2 (C.comap X.range.mkQ) ≤ d ∧
      Module.finrank F2 (F ⧸ D.map X.ker.subtype) ≤ d := by
  have hC := HybridComposition.finrank_comap_mkQ X.range C
  have hD := Submodule.finrank_map_subtype_eq X.ker D
  have hKD := D.finrank_quotient_add_finrank
  have hFD := (D.map X.ker.subtype).finrank_quotient_add_finrank
  have hX := X.finrank_range_add_finrank_ker
  change Module.finrank F2 X.range +
    (Module.finrank F2 C + Module.finrank F2 (X.ker ⧸ D)) ≤ d at hcut
  constructor <;> omega

/-- The native A.5 energy inequality with its actually proved numerical
complement factor. The only cutoff is the rank plus the outer derivative order. -/
theorem a5_energySquare_le_power (X : F →ₗ[F2] E)
    (C : Submodule F2 (E ⧸ X.range)) (D : Submodule F2 X.ker)
    [Fintype (OperatorPartitions.A5GeometricIndex X
      (C.comap X.range.mkQ) (D.map X.ker.subtype))]
    (d : ℕ) (hcut : Module.finrank F2 X.range + order C D ≤ d)
    (f : (E →ₗ[F2] F) → ℝ) (S : Parameter X.range X.ker) :
    (𝔼 N, hybridDerivative C D S (mapDerivative X f) N ^ 2) ^ 2 ≤
      (2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) *
        ∑ p : OperatorPartitions.A5GeometricIndex X
          (C.comap X.range.mkQ) (D.map X.ker.subtype),
          (𝔼 N, mapDerivative (LinearIdentities.compress X p.val.1 p.val.2)
            (hybridDerivative p.val.1 p.val.2 (embed X.range X.ker S) f) N ^ 2)^2 := by
  have hI : X.range ≤ C.comap X.range.mkQ := by
    intro x hx
    change X.range.mkQ x ∈ C
    have hz : X.range.mkQ x = 0 := by
      change x ∈ LinearMap.ker X.range.mkQ
      simpa only [Submodule.ker_mkQ] using hx
    rw [hz]
    exact C.zero_mem
  have hB : D.map X.ker.subtype ≤ X.ker := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact y.property
  have hCmap : (C.comap X.range.mkQ).map X.range.mkQ = C := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := X.range.mkQ_surjective x
      exact Submodule.mem_map.mpr ⟨y, hx, rfl⟩
  have hDcomap : (D.map X.ker.subtype).comap X.ker.subtype = D := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp hx
      have hxy : y = x := Subtype.ext heq
      simpa only [hxy] using hy
    · intro hx
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  have hdims := lifted_outer_dimensions X C D d hcut
  have hcount := A5IndexCount.card_geometricIndex_cube_le X
    (C.comap X.range.mkQ) (D.map X.ker.subtype) hI d hdims.1 hdims.2
  rw [Nat.card_eq_fintype_card] at hcount
  have hcountR :
      (Fintype.card (OperatorPartitions.A5GeometricIndex X
        (C.comap X.range.mkQ) (D.map X.ker.subtype)) : ℝ)^3 ≤
      (2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) := by exact_mod_cast hcount
  have hn := OperatorNorm.a5_energySquare_le X
    (C.comap X.range.mkQ) (D.map X.ker.subtype) hI hB f S
  have hfinal := hn.trans
    (mul_le_mul_of_nonneg_right hcountR
      (Finset.sum_nonneg (fun p _ => sq_nonneg _)))
  let energy (C' : Submodule F2 (E ⧸ X.range)) (D' : Submodule F2 X.ker) : ℝ :=
    (𝔼 N, hybridDerivative C' D' S (mapDerivative X f) N ^ 2)^2
  have he : energy ((C.comap X.range.mkQ).map X.range.mkQ)
      ((D.map X.ker.subtype).comap X.ker.subtype) = energy C D :=
    congrArg₂ energy hCmap hDcomap
  change energy ((C.comap X.range.mkQ).map X.range.mkQ)
      ((D.map X.ker.subtype).comap X.ker.subtype) ≤ _ at hfinal
  rw [he] at hfinal
  exact hfinal

theorem mapDerivative_hybridMomentSum_le (d e : ℕ) (X : F →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (hcut : Module.finrank F2 X.range + e ≤ d) :
    hybridMomentSum e (mapDerivative X f) ≤
      (2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) * postA5Sum X e f := by
  unfold hybridMomentSum postA5Sum
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  let : Fintype (OperatorPartitions.A5GeometricIndex X
      (s.val.1.comap X.range.mkQ) (s.val.2.map X.ker.subtype)) :=
    A5Passage.pairFintype X s
  have hs : Module.finrank F2 X.range + order s.val.1 s.val.2 ≤ d := by
    have ho := s.property
    omega
  calc
    (𝔼 S, (𝔼 N, hybridDerivative s.val.1 s.val.2 S (mapDerivative X f) N ^ 2)^2) ≤
        𝔼 S, (2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) *
          ∑ p : A5Passage.Pair X s,
            (𝔼 N, mapDerivative (LinearIdentities.compress X p.val.1 p.val.2)
              (hybridDerivative p.val.1 p.val.2 (embed X.range X.ker S) f) N ^ 2)^2 := by
      apply Finset.expect_le_expect
      intro S _
      exact a5_energySquare_le_power X s.val.1 s.val.2 d hs f S
    _ = _ := by rw [← Finset.mul_expect, Finset.expect_sum_comm]

/-- Recombination uses the natural domain and codomain isomorphisms. The
intermediate shifts need only be the actual embedded derivative parameters. -/
theorem postA5Sum_hybrid_average (A : Submodule F2 E) (B : Submodule F2 F)
    (X : B →ₗ[F2] (E ⧸ A)) (e : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 T, postA5Sum X e (hybridDerivative A B T f)) =
      A5Passage.descendantSum A B X e f := by
  unfold postA5Sum A5Passage.descendantSum
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [NaturalTransport.nested_mapDerivative_energy
    A B q.2.val.1 q.2.val.2 f]
  exact Restriction.real_translation_average
    (fun S : Parameter X.range X.ker => embed A B (embed X.range X.ker S))
    (fun U => (𝔼 N, mapDerivative
      (NaturalTransport.dualFactor A B q.2.val.1 q.2.val.2
        (LinearIdentities.compress X q.2.val.1 q.2.val.2))
      (hybridDerivative (q.2.val.1.comap A.mkQ) (q.2.val.2.map B.subtype) U f) N ^ 2)^2)

/-- The actual A.15 induction step for one positive-order derivative triple.
The induction hypothesis is used only at the strictly smaller degree `d-t`,
on its genuine quotient-domain and kernel-codomain spaces. -/
theorem a15_of_strong_induction (d t : ℕ) (A : Submodule F2 E)
    (B : Submodule F2 F) (X : B →ₗ[F2] (E ⧸ A))
    (ht : t = order A B + Module.finrank F2 X.range)
    (htpos : 0 < t) (htd : t ≤ d)
    (ih : ∀ e, e < d → BoundAtDegree.{u, v} e)
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) ≤
      (2 : ℝ) ^ (100 * (d - t) * (d - t) + 6 * d * Module.finrank F2 X.range) *
        A5Passage.descendantSum A B X (d - t) f := by
  have hlt : d - t < d := by omega
  have hcut : Module.finrank F2 X.range + (d - t) ≤ d := by omega
  have hpoint (T : E →ₗ[F2] F) :
      (𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) ≤
        (2 : ℝ) ^ (100 * (d - t) * (d - t) + 6 * d * Module.finrank F2 X.range) *
          postA5Sum X (d - t) (hybridDerivative A B T f) := by
    have hdeg : DegreeAtMost (d - t) (mapDerivative X (hybridDerivative A B T f)) := by
      simpa only [ht, frequencyRank] using degree_map_hybridDerivative A B X T f hf
    have hIH := ih (d - t) hlt (mapDerivative X (hybridDerivative A B T f)) hdeg
    have hnorm := mapDerivative_hybridMomentSum_le d (d - t) X
      (hybridDerivative A B T f) hcut
    calc
      (𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) ≤
          (2 : ℝ) ^ (100 * (d - t) * (d - t)) *
            hybridMomentSum (d - t) (mapDerivative X (hybridDerivative A B T f)) := hIH
      _ ≤ (2 : ℝ) ^ (100 * (d - t) * (d - t)) *
          ((2 : ℝ) ^ (6 * d * Module.finrank F2 X.range) *
            postA5Sum X (d - t) (hybridDerivative A B T f)) :=
        mul_le_mul_of_nonneg_left hnorm (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      _ = _ := by rw [pow_add]; ring
  calc
    (𝔼 T, 𝔼 N, mapDerivative X (hybridDerivative A B T f) N ^ 4) ≤
        𝔼 T, (2 : ℝ) ^ (100 * (d - t) * (d - t) + 6 * d * Module.finrank F2 X.range) *
          postA5Sum X (d - t) (hybridDerivative A B T f) :=
      Finset.expect_le_expect (fun T _ => hpoint T)
    _ = _ := by rw [← Finset.mul_expect, postA5Sum_hybrid_average]

/-- Apply the genuine lower-degree induction step to every term of the
checked A.13 sum, preserving its original positive-order cutoff. -/
theorem boundedTripleSum_le_descendants (d : ℕ)
    (ih : ∀ e, e < d → BoundAtDegree.{u, v} e)
    (f : (E →ₗ[F2] F) → ℝ) (hf : DegreeAtMost d f) :
    A13Reduction.boundedPositiveTripleSum d f ≤
      ∑ p : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
        (2 : ℝ) ^ (100 * (d - A13Index.size p.val)^2 +
          24 * d * A13Index.size p.val + 6 * d * Module.finrank F2 p.val.2.2.range) *
          A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
            (d - A13Index.size p.val) f := by
  unfold A13Reduction.boundedPositiveTripleSum
  apply Finset.sum_le_sum
  intro p _
  have h15 := a15_of_strong_induction d (A13Index.size p.val)
    p.val.1 p.val.2.1 p.val.2.2 rfl p.property.1 p.property.2 ih f hf
  have hw := mul_le_mul_of_nonneg_left h15
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (24 * d * A13Index.size p.val))
  have he : 24 * d * A13Index.size p.val +
      (100 * (d - A13Index.size p.val) * (d - A13Index.size p.val) +
        6 * d * Module.finrank F2 p.val.2.2.range) =
      100 * (d - A13Index.size p.val)^2 + 24 * d * A13Index.size p.val +
        6 * d * Module.finrank F2 p.val.2.2.range := by ring
  calc
    A13Reduction.tripleTerm d p.val f ≤
        (2 : ℝ) ^ (24 * d * A13Index.size p.val) *
          ((2 : ℝ) ^ (100 * (d - A13Index.size p.val) * (d - A13Index.size p.val) +
            6 * d * Module.finrank F2 p.val.2.2.range) *
            A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
              (d - A13Index.size p.val) f) := hw
    _ = ((2 : ℝ) ^ (24 * d * A13Index.size p.val) *
          (2 : ℝ) ^ (100 * (d - A13Index.size p.val) * (d - A13Index.size p.val) +
            6 * d * Module.finrank F2 p.val.2.2.range)) *
            A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
              (d - A13Index.size p.val) f := by ring
    _ = _ := by rw [← pow_add, he]

/-- Proposition A.5 on every finite-dimensional binary linear-map space,
proved by strong induction with all changing domains in the motive. -/
theorem boundAtDegree (d : ℕ) : BoundAtDegree.{u, v} d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro E F instE instME instF instMF instDE instDF instFiniteE instFiniteF
      instHom instDual f hf
    by_cases hz : d = 0
    · subst d
      exact degree_zero_bound f hf
    · have hd : 1 ≤ d := by omega
      have hreverse :
          (∑ p : A13Index.BoundedPositiveTriple (E := E) (F := F) d,
            (2 : ℝ) ^ (100 * (d - A13Index.size p.val)^2 +
              24 * d * A13Index.size p.val + 6 * d * Module.finrank F2 p.val.2.2.range) *
              A5Passage.descendantSum p.val.1 p.val.2.1 p.val.2.2
                (d - A13Index.size p.val) f) ≤
            (2 : ℝ) ^ (100 * d * d) * dampedHybridMoment d f := by
        simpa only [dampedHybridMoment, dampedMapMoment, frequencyRank, one_div] using
          A5ReverseSum.weighted_descendantSum_le d hd f
      have hbounded := (boundedTripleSum_le_descendants d ih f hf).trans hreverse
      have hA13 := A13Reduction.degree_reduction_truncated f d hf
      apply recurrence_closure d hd f hf
      simpa only [pow_two, Nat.mul_assoc] using
        hA13.trans (add_le_add le_rfl hbounded)

theorem derivative_inequality (d : ℕ) (f : (E →ₗ[F2] F) → ℝ)
    (hf : DegreeAtMost d f) :
    (𝔼 M, f M ^ 4) ≤ (2 : ℝ) ^ (100 * d ^ 2) * hybridMomentSum d f := by
  simpa only [pow_two, Nat.mul_assoc] using boundAtDegree.{u, v} d f hf

end Appendix.A5Induction

end UniqueGamesTheorem

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_MatrixSubspaceCount
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual subspace cardinality bounds used in (5.12)--(5.13).

Every subspace is the image of a projection endomorphism. Thus the set of all
subspaces is a quotient of the endomorphism space. The exact finite-field
linear-map count is reused from `Appendix.CompressionCount`.
-/

namespace UniqueGamesTheorem.Fourier.MatrixSubspaceCount

open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

section GeneralField

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Taking the image of an endomorphism reaches every actual subspace. -/
theorem endomorphism_range_surjective :
    Function.Surjective (fun f : V →ₗ[K] V => LinearMap.range f) := by
  intro S
  obtain ⟨T, hT⟩ := S.exists_isCompl
  exact ⟨S.projection T hT, Submodule.range_projection hT⟩

theorem card_subspaces_le_endomorphisms [Finite V] :
    Nat.card (Submodule K V) ≤ Nat.card (V →ₗ[K] V) := by
  let : Finite (V →ₗ[K] V) := Finite.of_injective
    (fun f : V →ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  exact Nat.card_le_card_of_surjective _ endomorphism_range_surjective

end GeneralField

section BinaryField

variable {C : Type*} [AddCommGroup C] [Module F2 C] [Module.Finite F2 C]

private theorem finite_color_space : Finite C :=
  Finite.of_injective (Module.finBasis F2 C).equivFun
    (Module.finBasis F2 C).equivFun.injective

theorem card_binary_subspaces_le :
    Nat.card (Submodule F2 C) ≤ 2 ^ (finrank F2 C * finrank F2 C) := by
  let : Finite C := finite_color_space
  calc
    _ ≤ Nat.card (C →ₗ[F2] C) := card_subspaces_le_endomorphisms
    _ = _ := UniqueGamesTheorem.Appendix.CompressionCount.natCard_linearMap

theorem card_binary_subspaces_le_of_finrank_le (s : ℕ) (hs : finrank F2 C ≤ s) :
    Nat.card (Submodule F2 C) ≤ 2 ^ (s * s) := by
  exact card_binary_subspaces_le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul hs hs))

end BinaryField

end UniqueGamesTheorem.Fourier.MatrixSubspaceCount

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Analysis_HybridCounting
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Gadget.StageQuotient.spaceFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFinite _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Quadratic.finiteBlockOrientation _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Frequency-conditioned counts of actual Hybrid pairs and derivative indices. -/
namespace UniqueGamesTheorem.Appendix.HybridCounting

open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

private theorem comap_subtype_injective {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (I A B : Submodule K V) (hA : A ≤ I) (hB : B ≤ I)
    (h : A.comap I.subtype = B.comap I.subtype) : A = B := by
  apply le_antisymm
  · intro x hx
    have hv : (⟨x, hA hx⟩ : I) ∈ A.comap I.subtype := hx
    rw [h] at hv
    exact hv
  · intro x hx
    have hv : (⟨x, hB hx⟩ : I) ∈ B.comap I.subtype := hx
    rw [← h] at hv
    exact hv

private theorem map_quotient_injective {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (N A B : Submodule K V) (hA : N ≤ A) (hB : N ≤ B)
    (h : A.map N.mkQ = B.map N.mkQ) : A = B := by
  have aux (P Q : Submodule K V) (hQ : N ≤ Q)
      (he : P.map N.mkQ = Q.map N.mkQ) : P ≤ Q := by
    intro x hx
    have hm : N.mkQ x ∈ P.map N.mkQ := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    rw [he] at hm
    obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp hm
    have hk : x - y ∈ N := by
      have hzero : x - y ∈ LinearMap.ker N.mkQ := by
        change N.mkQ (x - y) = 0
        rw [map_sub, heq, sub_self]
      simpa only [Submodule.ker_mkQ] using hzero
    have hz := Q.add_mem (hQ hk) hy
    simpa only [sub_add_cancel] using hz
  exact le_antisymm (aux A B hB h) (aux B A hA h.symm)

private theorem finite_submodules (V : Type*) [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V] : Finite (Submodule F2 V) := by
  let : Finite V := Finite.of_injective (Module.finBasis F2 V).equivFun
    (Module.finBasis F2 V).equivFun.injective
  exact Finite.of_injective (fun S : Submodule F2 V => (S : Set V)) SetLike.coe_injective

variable {E F : Type*} [AddCommGroup E] [AddCommGroup F]
  [Module F2 E] [Module F2 F] [FiniteDimensional F2 F]

/-- All actual Hybrid pairs for this frequency, with no ambient-dimension factor. -/
theorem card_hybrid_pairs_le (Y : F →ₗ[F2] E) (d : ℕ)
    (hY : finrank F2 Y.range ≤ d) :
    Nat.card {p : Submodule F2 E × Submodule F2 F //
      LinearIdentities.Hybrid Y p.1 p.2} ≤ 2 ^ (2 * d * d) := by
  classical
  let P := {p : Submodule F2 E × Submodule F2 F //
    LinearIdentities.Hybrid Y p.1 p.2}
  let : Finite (Submodule F2 Y.range) := finite_submodules _
  let : Finite (Submodule F2 (F ⧸ Y.ker)) := finite_submodules _
  have hk (p : P) : Y.ker ≤ p.1.2 := by
    intro x hx
    apply p.2.2
    change Y x ∈ p.1.1
    rw [show Y x = 0 from hx]
    exact Submodule.zero_mem _
  let code (p : P) : Submodule F2 Y.range × Submodule F2 (F ⧸ Y.ker) :=
    ((p.1.1).comap Y.range.subtype, (p.1.2).map Y.ker.mkQ)
  have hi : Function.Injective code := by
    intro p q h
    apply Subtype.ext
    apply Prod.ext
    · exact comap_subtype_injective Y.range p.1.1 q.1.1 p.2.1 q.2.1
        (congrArg Prod.fst h)
    · exact map_quotient_injective Y.ker p.1.2 q.1.2 (hk p) (hk q)
        (congrArg Prod.snd h)
  have hq : finrank F2 (F ⧸ Y.ker) = finrank F2 Y.range := by
    have hquot := Y.ker.finrank_quotient_add_finrank
    have hrank := Y.finrank_range_add_finrank_ker
    omega
  have hleft := UniqueGamesTheorem.Fourier.MatrixSubspaceCount.card_binary_subspaces_le_of_finrank_le
    (C := Y.range) d hY
  have hright := UniqueGamesTheorem.Fourier.MatrixSubspaceCount.card_binary_subspaces_le_of_finrank_le
    (C := F ⧸ Y.ker) d (hq.trans_le hY)
  calc
    _ ≤ Nat.card (Submodule F2 Y.range × Submodule F2 (F ⧸ Y.ker)) :=
      Nat.card_le_card_of_injective code hi
    _ = Nat.card (Submodule F2 Y.range) * Nat.card (Submodule F2 (F ⧸ Y.ker)) :=
      Nat.card_prod _ _
    _ ≤ 2 ^ (d * d) * 2 ^ (d * d) := Nat.mul_le_mul hleft hright
    _ = _ := by rw [← pow_add]; congr 1; ring

variable [FiniteDimensional F2 E]

/-- The actual order-bounded index subtype injects into the conditioned pairs. -/
theorem card_hybridIndex_le_two (Y : F →ₗ[F2] E) (d : ℕ)
    (hY : finrank F2 Y.range ≤ d) :
    Nat.card {s : Derivatives.HybridIndex (E := E) (F := F) d //
      LinearIdentities.Hybrid Y s.val.1 s.val.2} ≤ 2 ^ (2 * d * d) := by
  classical
  let : Finite (Submodule F2 E) := finite_submodules _
  let : Finite (Submodule F2 F) := finite_submodules _
  let code (s : {s : Derivatives.HybridIndex (E := E) (F := F) d //
      LinearIdentities.Hybrid Y s.val.1 s.val.2}) :
      {p : Submodule F2 E × Submodule F2 F // LinearIdentities.Hybrid Y p.1 p.2} :=
    ⟨s.1.1, s.2⟩
  have hi : Function.Injective code := by
    intro s t h
    apply Subtype.ext
    apply Subtype.ext
    change (code s).1 = (code t).1
    exact congrArg Subtype.val h
  exact (Nat.card_le_card_of_injective code hi).trans (card_hybrid_pairs_le Y d hY)

theorem card_hybridIndex_le (Y : F →ₗ[F2] E) (d : ℕ)
    (hY : finrank F2 Y.range ≤ d) :
    Nat.card {s : Derivatives.HybridIndex (E := E) (F := F) d //
      LinearIdentities.Hybrid Y s.val.1 s.val.2} ≤ 2 ^ (3 * d * d) := by
  apply (card_hybridIndex_le_two Y d hY).trans
  apply Nat.pow_le_pow_right (by decide)
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (d * d) (by decide : 2 ≤ 3)

end UniqueGamesTheorem.Appendix.HybridCounting

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAffineRestrictionPresentationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Actual Fourier components for the KMS analytic argument

All coefficients use normalized expectation on the primal matrix space; sums
over frequencies are unnormalized. These identities use only the common
trace-character Fourier infrastructure, not the legacy rank-level inequality.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixCharacters (linearTraceCharacter)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

@[simp] theorem coeff_synthesis (a : (F →ₗ[F2] E) → ℝ) (T : F →ₗ[F2] E) :
    linearCoeff (synthesis a) T = a T := by
  unfold synthesis
  rw [linearCoeff_sum]
  simp only [linearCoeff_smul, linearCoeff_character, mul_ite, mul_one, mul_zero]
  simp

@[simp] theorem coeff_component (P : (F →ₗ[F2] E) → Prop)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] E) :
    linearCoeff (component P f) T = if P T then linearCoeff f T else 0 := by
  exact coeff_synthesis _ _

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSAnalyticHybridEnergyImageTransportCoreLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The actual small-space Fourier component

An injection from the small domain into the large domain lifts dual
frequencies by composition. Only surjective small-space frequencies are
retained. The identities below use the actual trace-character coefficients
and normalized primal expectation; no fourth-moment estimate is assumed.
-/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier

variable {E F I : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup I] [Module F2 I]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F] [FiniteDimensional F2 I]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (I →ₗ[F2] F)] [Fintype (F →ₗ[F2] I)]

omit [FiniteDimensional F2 E] [Fintype (F →ₗ[F2] E)] in
@[simp] theorem coeff_smallComponent (ι : I →ₗ[F2] E)
    (f : (E →ₗ[F2] F) → ℝ) (T : F →ₗ[F2] I) :
    linearCoeff (smallComponent ι f) T = smallCoeff ι f T :=
  coeff_synthesis _ _

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

section

/-! The analytic synthesis and the direct basis-invariant projection are the
same actual function. This identity fixes the interface for both moment and
spectral estimates. -/

namespace UniqueGamesTheorem.Inverse.KMSAnalytic

noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Inverse.KMSBasisInvariant

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The degree bound follows from the literal coefficient filter. -/
theorem rankComponent_coeff_eq_zero_of_ne (i : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E)
    (hS : Module.finrank F2 S.range ≠ i) :
    linearCoeff (rankComponent i f) S = 0 := by
  simp only [rankComponent, coeff_component, ite_eq_right hS]

end
end UniqueGamesTheorem.Inverse.KMSAnalytic

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Inverse_KMSBasisComparisonPseudorandomTupleMapLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.DerivativeDegree

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- The actual selector multiplicity on frequencies of rank at most `d`.
This uses only the proved finite subspace count and Parseval. -/
theorem selector_energy_le (d : ℕ) (g : (E →ₗ[F2] F) → ℝ)
    (hg : DegreeAtMost d g) :
    hybridSelectorEnergy d g ≤ (2 : ℝ) ^ (3 * d * d) * (𝔼 X, g X ^ 2) := by
  unfold hybridSelectorEnergy hybridProjector
  apply selector_energy_sum_le
  intro Y hY
  have hrank : Module.finrank F2 Y.range ≤ d := by
    by_contra hn
    exact hY (hg Y (Nat.lt_of_not_ge hn))
  have hc := HybridCounting.card_hybridIndex_le Y d hrank
  have hcount : selectorMultiplicity
      (fun s : HybridIndex (E := E) (F := F) d =>
        fun Y => LinearIdentities.Hybrid Y s.val.1 s.val.2) Y =
      Nat.card {s : HybridIndex (E := E) (F := F) d //
        LinearIdentities.Hybrid Y s.val.1 s.val.2} := by
    simp only [selectorMultiplicity, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcount]
  exact_mod_cast hc

/-- Generic closure of the fourth-moment estimate from a uniform bound on
the actual hybrid derivatives. Its eventual KMS application must prove `hH`
from the basis-invariant function and its local densities. -/
theorem fourth_moment_le_of_uniform_hybrid_energy
    (d : ℕ) (g : (E →ₗ[F2] F) → ℝ) (hg : DegreeAtMost d g)
    (H : ℝ) (hH0 : 0 ≤ H)
    (hH : ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
      order A B ≤ d → (𝔼 N, hybridDerivative A B T g N ^ 2) ≤ H) :
    (𝔼 X, g X ^ 4) ≤ (2 : ℝ) ^ (103 * d * d) * H * (𝔼 X, g X ^ 2) := by
  have hp : (2 : ℝ) ^ (100 * d ^ 2) * (2 : ℝ) ^ (3 * d * d) =
      (2 : ℝ) ^ (103 * d * d) := by
    rw [← pow_add]
    congr 1
    ring
  calc
    (𝔼 X, g X ^ 4) ≤ (2 : ℝ) ^ (100 * d ^ 2) * hybridMomentSum d g :=
      A5Induction.derivative_inequality d g hg
    _ ≤ (2 : ℝ) ^ (100 * d ^ 2) * (H * hybridSelectorEnergy d g) :=
      mul_le_mul_of_nonneg_left (hybridMomentSum_le_of_uniform_energy d g H hH)
        (by positivity)
    _ ≤ (2 : ℝ) ^ (100 * d ^ 2) *
        (H * ((2 : ℝ) ^ (3 * d * d) * (𝔼 X, g X ^ 2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (selector_energy_le d g hg) hH0) (by positivity)
    _ = ((2 : ℝ) ^ (100 * d ^ 2) * (2 : ℝ) ^ (3 * d * d)) *
        H * (𝔼 X, g X ^ 2) := by ring
    _ = _ := by rw [hp]

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

section

/-!
The exact rank component meets the generic derivative inequality's degree
contract by its literal Fourier coefficient filter. This specializes the
checked aggregation to the same actual component used by the KMS spectral
argument; the separate basis-specific proof supplies its hybrid energy.
-/

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Inverse.KMSAnalytic
open UniqueGamesTheorem.Appendix
open UniqueGamesTheorem.Fourier.MatrixRestrictions

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Actual finite Fourier support of the component, with no rank-level
inequality invoked. -/
theorem rankComponent_degree (i : ℕ) (f : (E →ₗ[F2] F) → ℝ) :
    DerivativeDegree.DegreeAtMost i (rankComponent i f) := by
  intro S hS
  apply rankComponent_coeff_eq_zero_of_ne i f S
  exact ne_of_gt hS

variable [Finite E] [Finite F]

/-- Generic fourth-moment closure for the literal KMS rank component. -/
theorem rankComponent_fourth_moment_le_of_hybrid_oai (i : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (H : ℝ) (hH0 : 0 ≤ H)
    (hH : ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
      order A B ≤ i →
      (𝔼 N, Derivatives.hybridDerivative A B T (rankComponent i f) N ^ 2) ≤ H) :
    (𝔼 X, rankComponent i f X ^ 4) ≤
      (2 : ℝ) ^ (103 * i * i) * H * (𝔼 X, rankComponent i f X ^ 2) :=
  fourth_moment_le_of_uniform_hybrid_energy i (rankComponent i f)
    (rankComponent_degree i f) H hH0 hH

end
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.UniqueGamesTheorem.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid_oai.{u_1, u_2} := @OAI.UniqueGamesTheorem.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid_oai.{u_1, u_2}
