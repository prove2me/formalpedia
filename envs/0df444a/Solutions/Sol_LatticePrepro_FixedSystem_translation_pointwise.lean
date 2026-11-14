-- Prove2me | solution 1 for LatticePrepro.FixedSystem.translation_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:30:41.899575+00:00
-- url     : https://prove2.me/submissions/80e44eb0-ac38-4c8a-a6a9-472be1bda608

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Theorems.Thm_LatticePrepro_eq_zero_of_moment_eq_zero

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.FixedSystem end LatticePrepro.FixedSystem

namespace LatticePrepro

open Finsupp

section Moment

variable {F Ω : Type*} [CommRing F] [CommRing Ω] [Algebra F Ω]

/-- The moment map as an `F`-linear map. -/
noncomputable def momentₗ (k : ℕ) : (Ω →₀ F) →ₗ[F] Ω :=
  Finsupp.lsum F fun α => LinearMap.toSpanSingleton F Ω (α ^ k)

@[simp] lemma momentₗ_apply (f : Ω →₀ F) (k : ℕ) : momentₗ k f = moment f k := by
  simp only [momentₗ, moment, Finsupp.lsum_apply]
  rfl

lemma moment_sub (f g : Ω →₀ F) (k : ℕ) : moment (f - g) k = moment f k - moment g k := by
  simp only [← momentₗ_apply, map_sub]

lemma moment_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Ω →₀ F) (k : ℕ) :
    moment (∑ i ∈ s, f i) k = ∑ i ∈ s, moment (f i) k := by
  simp only [← momentₗ_apply, map_sum]

/-- Extend the scalars of a coefficient function along `algebraMap F Ω`. -/
noncomputable def extendScalars (f : Ω →₀ F) : Ω →₀ Ω :=
  f.mapRange (algebraMap F Ω) (map_zero _)

@[simp] lemma extendScalars_apply (f : Ω →₀ F) (α : Ω) :
    extendScalars f α = algebraMap F Ω (f α) := rfl

lemma moment_extendScalars (f : Ω →₀ F) (k : ℕ) : moment (extendScalars f) k = moment f k := by
  unfold moment extendScalars
  rw [sum_mapRange_index (by simp)]
  simp [Algebra.smul_def]

@[simp] lemma extendScalars_zero : extendScalars (0 : Ω →₀ F) = 0 := by
  ext; simp

end Moment

section Translation

variable {F Ω : Type*} [CommRing F] [CommRing Ω]

/-- The translation `α ↦ f (α - c)` of a coefficient function, i.e. the push-forward of `f`
along `α ↦ α + c`. -/
noncomputable def translate (c : Ω) (f : Ω →₀ F) : Ω →₀ F :=
  f.mapDomain (· + c)

lemma translate_apply (c : Ω) (f : Ω →₀ F) (α : Ω) : translate c f α = f (α - c) := by
  unfold translate
  have := Finsupp.mapDomain_apply' Set.univ f (Set.subset_univ _)
    (add_left_injective c).injOn (Set.mem_univ (α - c))
  simpa only [sub_add_cancel] using this

@[simp] lemma translate_single (c α : Ω) (a : F) :
    translate c (single α a) = single (α + c) a := by
  unfold translate; simp [Finsupp.mapDomain_single]

variable [Algebra F Ω]

/-- The binomial identity (20): the moments of a translation are linear combinations of the
lower-order moments. -/
lemma moment_translate (c : Ω) (f : Ω →₀ F) (k : ℕ) :
    moment (translate c f) k = ∑ j ∈ Finset.range (k + 1), (k.choose j : Ω) * c ^ (k - j) * moment f j := by
  unfold moment translate
  rw [Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => add_smul _ _ _)]
  simp only [Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [add_pow, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def]
  ring

/-- The moments of a translation difference, with the top term cancelled. -/
lemma moment_translate_sub (c : Ω) (f : Ω →₀ F) (k : ℕ) :
    moment (translate c f - f) k =
      ∑ j ∈ Finset.range k, (k.choose j : Ω) * c ^ (k - j) * moment f j := by
  rw [moment_sub, moment_translate, Finset.sum_range_succ]
  simp

end Translation

end LatticePrepro

namespace LatticePrepro

open Finsupp

namespace FixedSystem

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)

open Classical in
/-- The union of the supports of the represented functions of all tables. -/
noncomputable def suppUnion (f : V.TblIdx → Ω →₀ ZMod p) : Finset Ω :=
  Finset.univ.biUnion fun T => (f T).support

omit [Field Ω] [Algebra (ZMod p) Ω] in
lemma mem_suppUnion {f : V.TblIdx → Ω →₀ ZMod p} {T : V.TblIdx} {α : Ω} (h : f T α ≠ 0) :
    α ∈ suppUnion V f := by
  classical
  unfold suppUnion
  exact Finset.mem_biUnion.mpr ⟨T, Finset.mem_univ _, Finsupp.mem_support_iff.mpr h⟩

omit [Field Ω] [Algebra (ZMod p) Ω] in
lemma eq_zero_of_notMem_suppUnion {f : V.TblIdx → Ω →₀ ZMod p} {α : Ω}
    (h : α ∉ suppUnion V f) (T : V.TblIdx) : f T α = 0 :=
  by_contra fun h' => h (mem_suppUnion V h')

omit [Field Ω] [Algebra (ZMod p) Ω] in
lemma card_suppUnion_le (f : V.TblIdx → Ω →₀ ZMod p) :
    (suppUnion V f).card ≤ ∑ T, (f T).support.card := by
  classical
  unfold suppUnion
  exact Finset.card_biUnion_le

section Identities

variable {x : Fin V.n → Bool} {v : Col V R → ZMod p} (hv : Solves V R ε x v)
  (f : V.TblIdx → Ω →₀ ZMod p)
  (hf : ∀ T (k : R.Order), algebraMap K Ω (R.momentMap k (tbl V R v T)) = moment (f T) k)
  (hN : ∑ T, (f T).support.card < R.r)

include hv hf hN

/-- The translation identity holds pointwise (paper, §4.4). -/
private theorem translation_pointwise (α : Ω) :
    algebraMap (ZMod p) Ω (f (Sum.inl (V.rep 0 0)) α) -
      ∑ i : V.AuxIdx, (algebraMap (ZMod p) Ω (f (Sum.inr i) (α - algebraMap K Ω (ε.E i.1))) -
        algebraMap (ZMod p) Ω (f (Sum.inr i) α)) -
      Finsupp.single (algebraMap K Ω (V.instanceEnc ε x)) (1 : Ω) α = 0 := by
  classical
  set g : Ω →₀ Ω := extendScalars (f (Sum.inl (V.rep 0 0))) -
    ∑ i : V.AuxIdx, (translate (algebraMap K Ω (ε.E i.1)) (extendScalars (f (Sum.inr i))) -
      extendScalars (f (Sum.inr i))) - Finsupp.single (algebraMap K Ω (V.instanceEnc ε x)) 1
    with hg
  have hgapp : ∀ β, g β = algebraMap (ZMod p) Ω (f (Sum.inl (V.rep 0 0)) β) -
      ∑ i : V.AuxIdx, (algebraMap (ZMod p) Ω (f (Sum.inr i) (β - algebraMap K Ω (ε.E i.1))) -
        algebraMap (ZMod p) Ω (f (Sum.inr i) β)) -
      Finsupp.single (algebraMap K Ω (V.instanceEnc ε x)) (1 : Ω) β := by
    intro β
    simp [hg, translate_apply]
  -- support bound
  have hsum_aux : ∑ i : V.AuxIdx, (f (Sum.inr i)).support.card ≤ ∑ T, (f T).support.card := by
    rw [Fintype.sum_sum_type]
    exact Nat.le_add_left _ _
  set W : Finset Ω := suppUnion V f ∪
    (Finset.univ.biUnion fun i : V.AuxIdx =>
      (f (Sum.inr i)).support.map (addRightEmbedding (algebraMap K Ω (ε.E i.1))))
    ∪ {algebraMap K Ω (V.instanceEnc ε x)} with hW
  have hsupp : g.support ⊆ W := by
    intro β hβ
    rw [Finsupp.mem_support_iff] at hβ
    by_contra hβW
    apply hβ
    rw [hW, Finset.mem_union, Finset.mem_union, not_or, not_or] at hβW
    obtain ⟨⟨hβU, hβsh⟩, hβθ⟩ := hβW
    rw [Finset.mem_singleton] at hβθ
    have h1 : ∀ i : V.AuxIdx, f (Sum.inr i) (β - algebraMap K Ω (ε.E i.1)) = 0 := by
      intro i
      by_contra hne
      apply hβsh
      rw [Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ _, Finset.mem_map.mpr
        ⟨β - algebraMap K Ω (ε.E i.1), Finsupp.mem_support_iff.mpr hne, by simp⟩⟩
    rw [hgapp, eq_zero_of_notMem_suppUnion V hβU, map_zero, zero_sub,
      Finsupp.single_apply, if_neg (Ne.symm hβθ), sub_zero, neg_eq_zero]
    exact Finset.sum_eq_zero fun i _ => by
      rw [h1 i, eq_zero_of_notMem_suppUnion V hβU, map_zero, sub_self]
  have hcardW : W.card ≤ 2 * R.r - 1 := by
    have hr := R.two_le_r
    calc W.card ≤ ((suppUnion V f ∪ (Finset.univ.biUnion fun i : V.AuxIdx =>
          (f (Sum.inr i)).support.map (addRightEmbedding (algebraMap K Ω (ε.E i.1))))).card +
          ({algebraMap K Ω (V.instanceEnc ε x)} : Finset Ω).card) :=
          Finset.card_union_le _ _
      _ ≤ (suppUnion V f).card + (Finset.univ.biUnion fun i : V.AuxIdx =>
          (f (Sum.inr i)).support.map (addRightEmbedding (algebraMap K Ω (ε.E i.1)))).card + 1 := by
          rw [Finset.card_singleton]
          exact Nat.add_le_add_right (Finset.card_union_le _ _) 1
      _ ≤ (∑ T, (f T).support.card) + (∑ i : V.AuxIdx, (f (Sum.inr i)).support.card) + 1 := by
          refine Nat.add_le_add_right (Nat.add_le_add (card_suppUnion_le V f) ?_) 1
          refine Finset.card_biUnion_le.trans ?_
          simp [Finset.card_map]
      _ ≤ (∑ T, (f T).support.card) + (∑ T, (f T).support.card) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add_left hsum_aux _) 1
      _ ≤ 2 * R.r - 1 := by omega
  -- moments
  have hmom : ∀ k < 2 * R.r - 1, moment g k = 0 := by
    intro k hk
    have : moment g k = algebraMap K Ω (transLhs V R ε v ⟨k, hk⟩ - V.instanceEnc ε x ^ k) := by
      rw [transLhs, map_sub, map_sub, map_sum, map_pow, hg, moment_sub, moment_sub,
        moment_finset_sum, moment_extendScalars, moment_single, one_smul]
      unfold ptbl atbl
      rw [hf _ ⟨k, hk⟩]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [moment_translate_sub, map_sum, ← Fin.sum_univ_eq_sum_range (fun j =>
        (k.choose j : Ω) * algebraMap K Ω (ε.E i.1) ^ (k - j) *
          moment (extendScalars (f (Sum.inr i))) j) k]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [moment_extendScalars, map_mul, map_mul, map_pow, map_natCast,
        hf _ (R.below ⟨k, hk⟩ j), MomentRepresentation.below_val]
    rw [this, hv.translation ⟨k, hk⟩, sub_self, map_zero]
  have hg0 : g = 0 := eq_zero_of_moment_eq_zero g
    ((Finset.card_le_card hsupp).trans hcardW) hmom
  have h0 : g α = 0 := by rw [hg0]; rfl
  rw [hgapp] at h0
  exact h0

end Identities

end FixedSystem

end LatticePrepro

open LatticePrepro
open Finsupp
open LatticePrepro.FixedSystem
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)
variable {x : Fin V.n → Bool} {v : Col V R → ZMod p} (hv : Solves V R ε x v)
  (f : V.TblIdx → Ω →₀ ZMod p)
  (hf : ∀ T (k : R.Order), algebraMap K Ω (R.momentMap k (tbl V R v T)) = moment (f T) k)
  (hN : ∑ T, (f T).support.card < R.r)
include hv hf hN
theorem solution (α : Ω) :
    algebraMap (ZMod p) Ω (f (Sum.inl (V.rep 0 0)) α) -
      ∑ i : V.AuxIdx, (algebraMap (ZMod p) Ω (f (Sum.inr i) (α - algebraMap K Ω (ε.E i.1))) -
        algebraMap (ZMod p) Ω (f (Sum.inr i) α)) -
      Finsupp.single (algebraMap K Ω (V.instanceEnc ε x)) (1 : Ω) α = 0 :=
  @LatticePrepro.FixedSystem.translation_pointwise p _ K _ _ Ω _ _ _ _ V R ε x v hv f hf hN α
