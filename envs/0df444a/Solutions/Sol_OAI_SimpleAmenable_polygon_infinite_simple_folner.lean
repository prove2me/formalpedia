-- Prove2me | solution 1 for OAI.SimpleAmenable.polygon_infinite_simple_folner
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:50:23.116005+00:00
-- url     : https://prove2.me/submissions/dd978f78-f25f-4633-b1b0-d671248a2cd1

import Mathlib
import Definitions.Def_SimpleAmenable
import Definitions.Def_OAIQ65Sa009
import Definitions.Def_OAIQ65Sa010
import Theorems.Thm_OAI_SimpleAmenable_polygonFullGroup_finiteTestReiter

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_FiniteCoarea
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FiniteCoarea

variable {V E : Type*} [Fintype V] [Fintype E]

theorem finite_coarea (u v : E → V) (w : V → ℝ) (hw : ∀ x, 0 ≤ w x)
    (ε : ℝ) (h : graphVariation u v w < ε * ∑ x, w x) :
    ∃ A : Finset V, A.Nonempty ∧ (∀ x ∈ A, 0 < w x) ∧
      graphBoundary u v A < ε * A.card := by
  classical
  let S : Finset V := Finset.univ.filter (fun x => 0 < w x)
  suffices aux : ∀ n : ℕ, ∀ w : V → ℝ, (∀ x, 0 ≤ w x) →
      (Finset.univ.filter (fun x => 0 < w x)).card = n →
      graphVariation u v w < ε * ∑ x, w x →
      ∃ A : Finset V, A.Nonempty ∧ (∀ x ∈ A, 0 < w x) ∧
        graphBoundary u v A < ε * A.card from aux S.card w hw rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro w hw hn h
      let S : Finset V := Finset.univ.filter (fun x => 0 < w x)
      have hs : ∀ x, x ∈ S ↔ 0 < w x := by simp [S]
      have hS : S.Nonempty := by
        by_contra he
        have hz (x : V) : w x = 0 := by
          have : ¬ 0 < w x := fun hp => he ⟨x,(hs x).mpr hp⟩
          linarith [hw x]
        simp [graphVariation,hz] at h
      obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image S w hS
      let δ := w i
      have hd : 0 < δ := (hs i).mp hi
      let q : V → ℝ := fun x => if x ∈ S then w x - δ else 0
      have hq (x : V) : 0 ≤ q x := by
        dsimp only [q]
        split_ifs with hx
        · exact sub_nonneg.mpr (hmin x hx)
        · rfl
      have hw0 (x : V) (hx : x ∉ S) : w x = 0 := by
        have : ¬ 0 < w x := fun hp => hx ((hs x).mpr hp)
        linarith [hw x]
      have hwq (x : V) : w x = q x + δ * (if x ∈ S then 1 else 0) := by
        by_cases hx : x ∈ S
        · simp [q,hx]
        · simp [q,hx,hw0 x hx]
      have coeff (x y : V) :
          |w x - w y| = |q x - q y| + δ *
            |(if x ∈ S then (1 : ℝ) else 0) - (if y ∈ S then 1 else 0)| := by
        by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
        · simp [q,hx,hy]
        · have hqx : 0 ≤ w x - δ := by simpa [q,hx] using hq x
          simp only [q,hx,hy,ite_true,ite_false,hw0 y hy,sub_zero,abs_one,mul_one]
          rw [abs_of_nonneg (hw x),abs_of_nonneg hqx]
          ring
        · have hqy : 0 ≤ w y - δ := by simpa [q,hy] using hq y
          simp only [q,hx,hy,ite_true,ite_false,hw0 x hx,zero_sub,abs_neg,abs_one,mul_one]
          rw [abs_of_nonneg (hw y),abs_of_nonneg hqy]
          ring
        · simp [q,hx,hy,hw0 x hx,hw0 y hy]
      have hvar : graphVariation u v w = graphVariation u v q + δ * graphBoundary u v S := by
        unfold graphBoundary graphVariation
        simp_rw [coeff]
        rw [Finset.sum_add_distrib,Finset.mul_sum]
      have hmass : (∑ x, w x) = (∑ x, q x) + δ * S.card := by
        simp only [hwq,Finset.sum_add_distrib,← Finset.mul_sum]
        congr 1
        simp
      by_cases hb : graphBoundary u v S < ε * S.card
      · exact ⟨S,hS,fun x hx => (hs x).mp hx,hb⟩
      · have hrec : graphVariation u v q < ε * ∑ x, q x := by
          rw [hvar,hmass] at h
          have hbd : ε * S.card ≤ graphBoundary u v S := le_of_not_gt hb
          nlinarith
        let T := Finset.univ.filter (fun x => 0 < q x)
        have hTS : T ⊆ S := by
          intro x hx
          have hqx : 0 < q x := (Finset.mem_filter.mp hx).2
          by_contra hxS
          simp [q,hxS] at hqx
        have hiT : i ∉ T := by simp [T,q,hi,δ]
        have hc : T.card < n := by
          rw [← hn]
          exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨hTS,fun he => hiT (he.symm ▸ hi)⟩)
        obtain ⟨A,hA,hAw,hAb⟩ := ih T.card hc q hq rfl hrec
        refine ⟨A,hA,?_,hAb⟩
        intro x hx
        have hp := hAw x hx
        have hqS : x ∈ S := hTS (by simp [T,hp])
        exact (hs x).mp hqS

end FiniteCoarea

section WeightedGroupCoarea

variable {G : Type*} [Group G] [DecidableEq G]

theorem weighted_group_coarea (K S : Finset G) (p : G → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hs : ∀ x ∉ S, p x = 0) (ε : ℝ)
    (h : weightedVariation K S p < ε * ∑ x ∈ S, p x) :
    ∃ D : Finset G, D.Nonempty ∧ D ⊆ S ∧
      (∑ k ∈ K, ((symmDiff (D.image (fun x => k*x)) D).card : ℝ)) < ε * D.card := by
  classical
  let B := translationWindow K S
  let node : G → Option {x // x ∈ S} := fun x => if hx : x ∈ S then some ⟨x,hx⟩ else none
  let w : Option {x // x ∈ S} → ℝ := fun z => match z with
    | none => 0
    | some x => p x.val
  let u : {k // k ∈ K} × {x // x ∈ B} → Option {x // x ∈ S} :=
    fun e => node (e.1.val⁻¹ * e.2.val)
  let v : {k // k ∈ K} × {x // x ∈ B} → Option {x // x ∈ S} :=
    fun e => node e.2.val
  have hwnode (x : G) : w (node x) = p x := by
    by_cases hx : x ∈ S
    · simp [node,w,hx]
    · simp [node,w,hx,hs x hx]
  have hw : ∀ z, 0 ≤ w z := by intro z; cases z with
    | none => exact le_rfl
    | some z => exact hp z.val
  have hm : (∑ z, w z) = ∑ x ∈ S, p x := by
    simp [w,Fintype.sum_option,Finset.sum_attach]
  have hv : graphVariation u v w = weightedVariation K S p := by
    simp only [graphVariation,Fintype.sum_prod_type,u,v,hwnode]
    unfold weightedVariation
    rw [← Finset.sum_coe_sort K]
    apply Fintype.sum_congr
    intro k
    rw [← Finset.sum_coe_sort (translationWindow K S)]
  obtain ⟨A,hA,hpos,hbd⟩ := finite_coarea u v w hw ε (by rwa [hv,hm])
  have hn : (none : Option {x // x ∈ S}) ∉ A := by
    intro hn
    have hh := hpos none hn
    exact (lt_irrefl 0) hh
  let D : Finset G := S.filter (fun x => node x ∈ A)
  have hDS : D ⊆ S := Finset.filter_subset _ _
  have hnode (x : G) : node x ∈ A ↔ x ∈ D := by
    by_cases hx : x ∈ S
    · simp [D,hx]
    · simp [node,D,hx,hn]
  have hmap : D.image node = A := by
    ext z
    constructor
    · rintro hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact (hnode x).mpr hx
    · intro hz
      cases z with
      | none => exact False.elim (hn hz)
      | some x =>
          have he : node x.val = some x := by simp [node,x.property]
          exact Finset.mem_image.mpr ⟨x.val,(hnode x.val).mp (he ▸ hz),he⟩
  have hc : A.card = D.card := by
    rw [← hmap]
    apply Finset.card_image_iff.mpr
    intro x hx y hy he
    have hxS := hDS hx
    have hyS := hDS hy
    simp only [node,hxS,hyS,dite_eq_left,Option.some.injEq,Subtype.mk.injEq] at he
    exact he
  have hDn : D.Nonempty := by
    rw [← hmap] at hA
    exact Finset.Nonempty.of_image hA
  have hb (k : G) (hk : k ∈ K) : symmDiff (D.image (fun x => k*x)) D ⊆ B := by
    intro x hx
    have hx' := Finset.mem_symmDiff.mp hx
    rcases hx' with ⟨him,_⟩ | ⟨hD,_⟩
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp him
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨k,hk,Finset.mem_image.mpr ⟨y,hDS hy,rfl⟩⟩)
    · exact Finset.mem_union_left _ (hDS hD)
  have hf (k x : G) :
      |(if node (k⁻¹*x) ∈ A then (1 : ℝ) else 0) -
        (if node x ∈ A then 1 else 0)| =
      if x ∈ symmDiff (D.image (fun y => k*y)) D then 1 else 0 := by
    have hi : x ∈ D.image (fun y => k*y) ↔ k⁻¹*x ∈ D := by
      constructor
      · rintro h
        obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
        simpa using hy
      · intro hx
        exact Finset.mem_image.mpr ⟨k⁻¹*x,hx,by group⟩
    simp only [hnode,Finset.mem_symmDiff,hi]
    by_cases h1 : k⁻¹*x ∈ D <;> by_cases h2 : x ∈ D <;> simp [h1,h2]
  have hbound : graphBoundary u v A =
      ∑ k ∈ K, ((symmDiff (D.image (fun x => k*x)) D).card : ℝ) := by
    unfold graphBoundary graphVariation
    simp only [u,v]
    rw [Fintype.sum_prod_type]
    rw [← Finset.sum_coe_sort K]
    apply Fintype.sum_congr
    intro k
    have hinner : (∑ x : B, |(if node (k.val⁻¹*x.val) ∈ A then (1 : ℝ) else 0) -
        (if node x.val ∈ A then 1 else 0)|) =
        ∑ x : B, if x.val ∈ symmDiff (D.image (fun y => k.val*y)) D then (1 : ℝ) else 0 := by
      apply Fintype.sum_congr
      intro x
      exact hf k.val x.val
    refine Eq.trans ?_ hinner |>.trans ?_
    · apply Fintype.sum_congr
      intro x
      split_ifs <;> simp_all
    have hcSum := Finset.sum_coe_sort B (fun (x : G) =>
      if x ∈ symmDiff (D.image (fun y => k.val*y)) D then (1 : ℝ) else 0)
    have he : B.filter (fun x => x ∈ symmDiff (D.image (fun x => k.val*x)) D) =
        symmDiff (D.image (fun x => k.val*x)) D := by
      exact Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (hb k.val k.property))
    calc
      _ = ∑ x ∈ B, if x ∈ symmDiff (D.image (fun y => k.val*y)) D then (1 : ℝ) else 0 := by
        simpa using hcSum
      _ = _ := by rw [Finset.sum_boole,he]
  refine ⟨D,hDn,hDS,?_⟩
  rwa [hbound,hc] at hbd

end WeightedGroupCoarea

theorem folner_of_finite_reiter {G : Type*} [Group G]
    (h : FiniteSupportReiter G) : FolnerAmenable G := by
  classical
  intro K ε hε
  obtain ⟨S,p,hp,hs,hm,hv⟩ := h K ε hε
  obtain ⟨D,hD,_,hb⟩ := weighted_group_coarea K S p hp hs ε (by simpa only [hm,mul_one] using hv)
  refine ⟨D,hD,?_⟩
  intro k hk
  have hn (j : G) (_ : j ∈ K) : 0 ≤ ((symmDiff (D.image (fun x => j*x)) D).card : ℝ) :=
    Nat.cast_nonneg _
  have hi := Finset.single_le_sum hn hk
  exact lt_of_le_of_lt hi hb

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonAction
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section PolygonAction

private theorem exists_in_interval_avoiding (l r : ℝ) (hlr : l < r)
    (S : Set ℝ) (hS : S.Countable) : ∃ x ∈ Set.Ioo l r, x ∉ S := by
  apply Set.not_subset.mp
  intro h
  have := Cardinal.Real.Ioo_countable_iff.mp (hS.mono h)
  linarith

theorem generic_rectangle (a : ℕ) (l₁ r₁ l₂ r₂ : ℝ)
    (hl₁ : 0 ≤ l₁) (hr₁ : r₁ ≤ 1) (h₁ : l₁ < r₁)
    (hl₂ : 0 ≤ l₂) (hr₂ : r₂ ≤ 1) (h₂ : l₂ < r₂) :
    ∃ p : GenericSquare a, p.val.1 ∈ Set.Ioo l₁ r₁ ∧ p.val.2 ∈ Set.Ioo l₂ r₂ := by
  obtain ⟨x, hx, hx'⟩ := exists_in_interval_avoiding l₁ r₁ h₁
    (Set.range ordinary) (Set.countable_range ordinary)
  let t := Real.goldenRatio ^ a
  have ht : t ≠ 0 := ne_of_gt (pow_pos Real.goldenRatio_pos a)
  let S := Set.range ordinary ∪ Set.range (fun z : CutRing => ordinary z + t*x) ∪
    Set.range (fun z : CutRing => (x - ordinary z)/t)
  have hS : S.Countable := ((Set.countable_range ordinary).union
    (Set.countable_range _)).union (Set.countable_range _)
  obtain ⟨y, hy, hy'⟩ := exists_in_interval_avoiding l₂ r₂ h₂ S hS
  have hav : AvoidsCuts a (x,y) := by
    intro j z hz
    fin_cases j
    · exact hx' ⟨z, by simpa [cutForm] using hz.symm⟩
    · apply hy'
      exact Or.inl (Or.inl ⟨z, by simpa [cutForm] using hz.symm⟩)
    · apply hy'
      apply Or.inl ∘ Or.inr
      refine ⟨z, ?_⟩
      change ordinary z + t*x = y
      change y - t*x = ordinary z at hz
      linarith
    · apply hy'
      apply Or.inr
      refine ⟨z, ?_⟩
      apply (div_eq_iff ht).mpr
      change x - t*y = ordinary z at hz
      linarith
  exact ⟨⟨(x,y), ⟨by linarith [hx.1], by linarith [hx.2]⟩,
    ⟨by linarith [hy.1], by linarith [hy.2]⟩, hav⟩, hx, hy⟩

instance instNonemptyGenericSquare (a : ℕ) : Nonempty (GenericSquare a) := by
  obtain ⟨p, _⟩ := generic_rectangle a 0 1 0 1 le_rfl le_rfl zero_lt_one le_rfl le_rfl zero_lt_one
  exact ⟨p⟩

end PolygonAction

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TupleChartDomain
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section PolygonFullGroup
attribute [local instance] Classical.propDecidable

theorem conditional_cycle_injective {a m : ℕ} (ι : Fin 3 ↪ Fin m) :
    Function.Injective (fun U : polygonAlgebra a => conditionalHom U (trackCycle ι)) := by
  classical
  intro U V h
  apply Subtype.ext
  ext x
  have he := congrArg (fun g : polygonFullGroup a m => g.val (ι 0,x)) h
  change conditionalPerm U (trackCycle ι) (ι 0,x) =
    conditionalPerm V (trackCycle ι) (ι 0,x) at he
  have h01 : ι 0 ≠ ι 1 := ι.injective.ne (by decide)
  by_cases hu : x ∈ U.val <;> by_cases hv : x ∈ V.val <;>
    simp [hu, hv, trackCycle_apply] at he ⊢

theorem shrinkingLevel_strictAnti : StrictAnti (fun n => ordinary (shrinkingLevel n)) := by
  intro n k hnk
  simp only [ordinary_shrinkingLevel]
  exact pow_lt_pow_right_of_lt_one₀ (sub_pos.mpr Real.one_lt_goldenRatio)
    (by linarith [Real.goldenRatio_lt_two]) (by omega)

theorem shrinkingPolygon_injective (a : ℕ) : Function.Injective (shrinkingPolygon a) := by
  suffices h : ∀ n k : ℕ, n < k → shrinkingPolygon a n ≠ shrinkingPolygon a k by
    intro n k he
    rcases lt_trichotomy n k with hlt | heq | hgt
    · exact False.elim (h n k hlt he)
    · exact heq
    · exact False.elim (h k n hgt he.symm)
  intro n k hnk he
  obtain ⟨p,hx,_⟩ := generic_rectangle a (ordinary (shrinkingLevel k))
    (ordinary (shrinkingLevel n)) 0 1 (shrinkingLevel_bounds k).1.le
    (shrinkingLevel_bounds n).2.le (shrinkingLevel_strictAnti hnk)
    le_rfl le_rfl zero_lt_one
  have hn : p ∈ (shrinkingPolygon a n).val := by
    exact hx.2
  have hk : p ∉ (shrinkingPolygon a k).val := by
    change ¬ p.val.1 < ordinary (shrinkingLevel k)
    linarith [hx.1]
  exact hk (he ▸ hn)

theorem polygonAlternatingGroup_infinite (a m : ℕ) (hm : 3 ≤ m) :
    Infinite (polygonAlternatingGroup a m) := by
  let ι := Fin.castLEEmb hm
  let f : ℕ → polygonAlternatingGroup a m := fun n =>
    ⟨conditionalHom (shrinkingPolygon a n) (trackCycle ι),
      conditional_cycle_mem (shrinkingPolygon a n) ι⟩
  apply Infinite.of_injective f
  intro n k h
  apply shrinkingPolygon_injective a
  apply conditional_cycle_injective ι
  exact congrArg Subtype.val h

end PolygonFullGroup
end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_Supported
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section LocalDisplacement

theorem supported_disjoint_commute {α : Type*} {f g : Equiv.Perm α}
    {U V : Set α} (hf : SupportedIn f U) (hg : SupportedIn g V)
    (hUV : Disjoint U V) : Commute f g := by
  apply Equiv.Perm.Disjoint.commute
  intro p
  by_cases hp : p ∈ U
  · exact Or.inr (hg p (fun h => Set.disjoint_left.mp hUV hp h))
  · exact Or.inl (hf p hp)

open scoped commutatorElement in
theorem double_commutator_of_displacement {G : Type*} [Group G] (n a b : G)
    (ha : Commute (n*a*n⁻¹) a) (hb : Commute (n*a*n⁻¹) b) :
    ⁅⁅n,a⁆,b⁆ = ⁅a⁻¹,b⁆ := by
  have hc : Commute (n*a*n⁻¹) ⁅a⁻¹,b⁆ := by
    simpa only [commutatorElement_def, inv_inv] using
      ((ha.inv_right.mul_right hb).mul_right ha).mul_right hb.inv_right
  change ⁅(n*a*n⁻¹)*a⁻¹,b⁆ = _
  rw [commutatorElement_mul_left_eq_conj_mul, hb.commutator_eq, mul_one,
    hc.eq, mul_assoc, mul_inv_cancel, mul_one]

open scoped commutatorElement in

theorem supported_double_commutator {α : Type*} (n a b : Equiv.Perm α)
    (U : Set α) (ha : SupportedIn a U) (hb : SupportedIn b U)
    (hdis : Disjoint U (n '' U)) : ⁅⁅n,a⁆,b⁆ = ⁅a⁻¹,b⁆ := by
  exact double_commutator_of_displacement n a b
    (supported_disjoint_commute (supported_conjugate n ha) ha hdis.symm)
    (supported_disjoint_commute (supported_conjugate n ha) hb hdis.symm)

theorem halfPlane_isClopen (a : ℕ) (j : Fin 4) (c : CutRing) :
    IsClopen (halfPlane a j c) := by
  have hc : Continuous (fun p : GenericSquare a => cutForm a j p.val) :=
    (cutForm_continuous a j).comp continuous_subtype_val
  have hopen : IsOpen (halfPlane a j c) := isOpen_lt hc continuous_const
  have he : (halfPlane a j c)ᶜ = {p : GenericSquare a | ordinary c < cutForm a j p.val} := by
    ext p
    simp only [Set.mem_compl_iff, halfPlane, Set.mem_ofPred_eq, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (p.property.2.2 j c).symm, le_of_lt⟩
  exact ⟨isOpen_compl_iff.mp (he ▸ isOpen_lt continuous_const hc), hopen⟩

theorem polygon_isClopen {a : ℕ} (U : polygonAlgebra a) : IsClopen U.val := by
  apply polygon_induction (P := IsClopen) (fun j c => halfPlane_isClopen a j c)
    isClopen_empty (fun _ _ h k => h.union k) (fun _ h => h.compl) U.property

theorem polygon_contains_rectangle {a : ℕ} (U : polygonAlgebra a)
    (hU : U.val.Nonempty) :
    ∃ l r : CutRing × CutRing,
      0 < ordinary l.1 ∧ ordinary l.1 < ordinary r.1 ∧ ordinary r.1 < 1 ∧
      0 < ordinary l.2 ∧ ordinary l.2 < ordinary r.2 ∧ ordinary r.2 < 1 ∧
      ∀ p : GenericSquare a,
        (ordinary l.1 < p.val.1 ∧ p.val.1 < ordinary r.1) →
        (ordinary l.2 < p.val.2 ∧ p.val.2 < ordinary r.2) → p ∈ U.val := by
  obtain ⟨p,hp⟩ := hU
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (polygon_isClopen U).isOpen p hp
  have hp0 := generic_coordinates_pos p
  obtain ⟨l₁,hl₁,hlp⟩ := exists_cut_between
    (show max 0 (p.val.1-ε) < p.val.1 by exact max_lt hp0.1 (sub_lt_self _ hε))
  obtain ⟨l₂,hl₂,hlq⟩ := exists_cut_between
    (show max 0 (p.val.2-ε) < p.val.2 by exact max_lt hp0.2 (sub_lt_self _ hε))
  obtain ⟨r₁,hpr,hr₁⟩ := exists_cut_between
    (show p.val.1 < min 1 (p.val.1+ε) by exact lt_min p.property.1.2 (lt_add_of_pos_right _ hε))
  obtain ⟨r₂,hqr,hr₂⟩ := exists_cut_between
    (show p.val.2 < min 1 (p.val.2+ε) by exact lt_min p.property.2.1.2 (lt_add_of_pos_right _ hε))
  refine ⟨(l₁,l₂),(r₁,r₂),lt_of_le_of_lt (le_max_left _ _) hl₁,
    hlp.trans hpr,(lt_min_iff.mp hr₁).1,?_,hlq.trans hqr,(lt_min_iff.mp hr₂).1,?_⟩
  · exact lt_of_le_of_lt (le_max_left _ _) hl₂
  · intro q hqx hqy
    apply hball
    change max (dist q.val.1 p.val.1) (dist q.val.2 p.val.2) < ε
    rw [max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt]
    have hx := (max_lt_iff.mp hl₁).2
    have hy := (max_lt_iff.mp hl₂).2
    have hx' := (lt_min_iff.mp hr₁).2
    have hy' := (lt_min_iff.mp hr₂).2
    constructor <;> constructor <;> linarith

theorem mem_smallSquare {a : ℕ} (d : CutRing) (p : GenericSquare a) :
    p ∈ (smallSquare a d).val ↔ p.val.1 < ordinary d ∧ p.val.2 < ordinary d := Iff.rfl

theorem fiveRectangleShifts_val {a : ℕ} (l : CutRing × CutRing) (d : CutRing)
    (hlx : 0 < ordinary l.1) (hly : 0 < ordinary l.2)
    (hd : 0 < ordinary d) (hx1 : ordinary l.1 + 9*ordinary d < 1)
    (hy1 : ordinary l.2 + ordinary d < 1) (i : Fin 5)
    (p : (smallSquare a d).val) :
    (translate a (fiveRectangleShifts l d i) p.val).val =
      (p.val.val.1 + ordinary l.1 + 2*(i.val : ℝ)*ordinary d,
       p.val.val.2 + ordinary l.2) := by
  have hp0 := generic_coordinates_pos p.val
  have hpd := (mem_smallSquare d p.val).mp p.property
  have hi : (i.val : ℝ) ≤ 4 := by exact_mod_cast (show i.val ≤ 4 by omega)
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  simp only [translate_val, fiveRectangleShifts, map_add, map_mul, map_ofNat, map_natCast]
  rw [Int.fract_eq_self.mpr ⟨by nlinarith, by nlinarith⟩,
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  congr 1
  ring

theorem five_slots_in_polygon {a m : ℕ} (U : polygonAlgebra a)
    (hU : U.val.Nonempty) (t : Fin m) :
    ∃ d : CutRing, 0 < ordinary d ∧ ordinary d < 1 ∧
    ∃ slots : Fin 5 → Fin m × (CutRing × CutRing),
      Function.Injective (SlotMap a m (smallSquare a d) slots) ∧
      Set.range (SlotMap a m (smallSquare a d) slots) ⊆ {p | p.1 = t ∧ p.2 ∈ U.val} := by
  obtain ⟨l,r,hlx,hlr,hrx,hly,hlr',hry,hrect⟩ := polygon_contains_rectangle U hU
  obtain ⟨d,hd,hdlim⟩ := exists_cut_between
    (show (0:ℝ) < min ((ordinary r.1-ordinary l.1)/10) ((ordinary r.2-ordinary l.2)/2) by
      exact lt_min (div_pos (sub_pos.mpr hlr) (by norm_num))
        (div_pos (sub_pos.mpr hlr') (by norm_num)))
  have hxlim := (lt_min_iff.mp hdlim).1
  have hylim := (lt_min_iff.mp hdlim).2
  have hsmall : ordinary d < 1 := by linarith
  have hx1 : ordinary l.1 + 9*ordinary d < 1 := by linarith
  have hy1 : ordinary l.2 + ordinary d < 1 := by linarith
  let slots : Fin 5 → Fin m × (CutRing × CutRing) := fun i => (t,fiveRectangleShifts l d i)
  have hv (i : Fin 5) (p : (smallSquare a d).val) :=
    fiveRectangleShifts_val l d hlx hly hd hx1 hy1 i p
  refine ⟨d,hd,hsmall,slots,?_,?_⟩
  · rintro ⟨i,x⟩ ⟨j,y⟩ he
    have hx := (mem_smallSquare d x.val).mp x.property
    have hy := (mem_smallSquare d y.val).mp y.property
    have hx0 := generic_coordinates_pos x.val
    have hy0 := generic_coordinates_pos y.val
    have hh := congrArg (fun p : TrackPoint a m => p.2.val.1) he
    change (translate a (fiveRectangleShifts l d i) x.val).val.1 =
      (translate a (fiveRectangleShifts l d j) y.val).val.1 at hh
    rw [hv i x,hv j y] at hh
    have hij : i = j := by
      apply Fin.ext
      rcases lt_trichotomy i.val j.val with h | h | h
      · have h' : (i.val : ℝ)+1 ≤ j.val := by exact_mod_cast h
        nlinarith
      · exact h
      · have h' : (j.val : ℝ)+1 ≤ i.val := by exact_mod_cast h
        nlinarith
    subst j
    refine Prod.ext rfl ?_
    apply Subtype.ext
    exact (translation a (fiveRectangleShifts l d i)).injective (congrArg Prod.snd he)
  · rintro p ⟨⟨i,x⟩,rfl⟩
    refine ⟨rfl,?_⟩
    apply hrect
    · change ordinary l.1 < (translate a (fiveRectangleShifts l d i) x.val).val.1 ∧
        (translate a (fiveRectangleShifts l d i) x.val).val.1 < ordinary r.1
      rw [hv i x]
      have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
      have hi4 : (i.val : ℝ) ≤ 4 := by exact_mod_cast (show i.val ≤ 4 by omega)
      have hx := (mem_smallSquare d x.val).mp x.property
      have hx0 := generic_coordinates_pos x.val
      constructor <;> nlinarith
    · change ordinary l.2 < (translate a (fiveRectangleShifts l d i) x.val).val.2 ∧
        (translate a (fiveRectangleShifts l d i) x.val).val.2 < ordinary r.2
      rw [hv i x]
      have hx := (mem_smallSquare d x.val).mp x.property
      have hx0 := generic_coordinates_pos x.val
      constructor <;> linarith

private theorem floor_remainder_bounds {a : ℕ} (d : CutRing) (hd : 0 < ordinary d)
    (p : GenericSquare a) (j : Fin 2) :
    let x := ![p.val.1,p.val.2] j
    0 < x - (⌊x/ordinary d⌋ : ℝ)*ordinary d ∧
      x - (⌊x/ordinary d⌋ : ℝ)*ordinary d < ordinary d := by
  dsimp
  let x := ![p.val.1,p.val.2] j
  have hlo : (⌊x/ordinary d⌋ : ℝ)*ordinary d ≤ x :=
    (le_div_iff₀ hd).mp (Int.floor_le _)
  have hhi : x < ((⌊x/ordinary d⌋ : ℝ)+1)*ordinary d :=
    (div_lt_iff₀ hd).mp (Int.lt_floor_add_one _)
  have hne : x ≠ (⌊x/ordinary d⌋ : ℝ)*ordinary d := by
    fin_cases j
    · simpa [x,cutForm] using p.property.2.2 0 ((⌊p.val.1/ordinary d⌋ : ℤ)*d)
    · simpa [x,cutForm] using p.property.2.2 1 ((⌊p.val.2/ordinary d⌋ : ℤ)*d)
  constructor <;> dsimp [x] at *
  · exact sub_pos.mpr (lt_of_le_of_ne hlo (fun h => hne h.symm))
  · linarith

theorem smallSquare_finite_translated_cover (a : ℕ) (d : CutRing)
    (hd : 0 < ordinary d) (hd1 : ordinary d < 1) :
    ∃ s : Finset (CutRing × CutRing), ∀ p : GenericSquare a,
      ∃ u ∈ s, p ∈ (translatedPolygon u (smallSquare a d)).val := by
  classical
  let I := Finset.Icc (0 : ℤ) ⌈1/ordinary d⌉
  let shift : ℤ × ℤ → CutRing × CutRing := fun k => ((k.1 : CutRing)*d,(k.2 : CutRing)*d)
  refine ⟨(I ×ˢ I).image shift,?_⟩
  intro p
  let k : ℤ × ℤ := (⌊p.val.1/ordinary d⌋,⌊p.val.2/ordinary d⌋)
  have hk : k ∈ I ×ˢ I := by
    have hb (x : ℝ) (hx : x ∈ Set.Ico 0 1) : ⌊x/ordinary d⌋ ∈ I := by
      rw [Finset.mem_Icc]
      refine ⟨Int.floor_nonneg.mpr (div_nonneg hx.1 hd.le),?_⟩
      exact (Int.floor_mono (div_le_div_of_nonneg_right hx.2.le hd.le)).trans
        (Int.floor_le_ceil (1/ordinary d))
    exact Finset.mem_product.mpr ⟨hb _ p.property.1,hb _ p.property.2.1⟩
  have hx := floor_remainder_bounds d hd p 0
  have hy := floor_remainder_bounds d hd p 1
  dsimp at hx hy
  let q := translate a (-(shift k)) p
  have hq : q.val = (p.val.1-(k.1:ℝ)*ordinary d,p.val.2-(k.2:ℝ)*ordinary d) := by
    simp only [q,translate_val, Prod.fst_neg,Prod.snd_neg,map_neg,shift,map_mul,map_intCast]
    rw [← sub_eq_add_neg,← sub_eq_add_neg]
    rw [Int.fract_eq_self.mpr ⟨hx.1.le,hx.2.trans hd1⟩,
        Int.fract_eq_self.mpr ⟨hy.1.le,hy.2.trans hd1⟩]
  refine ⟨shift k,Finset.mem_image.mpr ⟨k,hk,rfl⟩,q,?_,?_⟩
  · rw [mem_smallSquare,hq]
    exact ⟨hx.2,hy.2⟩
  · change translate a (shift k) (translate a (-(shift k)) p) = p
    rw [← translate_add, add_neg_cancel, translate_zero]

theorem bankPermutation_even : bankPermutation ∈ alternatingGroup (Fin 9) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem bankSlots_injective {a m : ℕ} (U : polygonAlgebra a)
    (b : Fin 3 → Fin 3 → Fin m × (CutRing × CutRing))
    (hb : ∀ i, Function.Injective (SlotMap a m U (b i)))
    (hdis : ∀ i j, i ≠ j → Disjoint (Set.range (SlotMap a m U (b i)))
      (Set.range (SlotMap a m U (b j)))) :
    Function.Injective (SlotMap a m U (bankSlots b)) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  obtain ⟨⟨i₁,i₂⟩,rfl⟩ := bankIndex.surjective i
  obtain ⟨⟨j₁,j₂⟩,rfl⟩ := bankIndex.surjective j
  have he' : SlotMap a m U (b i₁) (i₂,x) = SlotMap a m U (b j₁) (j₂,y) := by
    simpa only [SlotMap,bankSlots_apply] using he
  have hij : i₁ = j₁ := by
    by_contra hn
    exact Set.disjoint_left.mp (hdis i₁ j₁ hn) ⟨(i₂,x),rfl⟩ ⟨(j₂,y),he'.symm⟩
  subst j₁
  have hh := hb i₁ he'
  obtain ⟨h₁,h₂⟩ := Prod.mk.inj hh
  subst j₂
  subst y
  rfl

theorem transport_bank {a m : ℕ} (U : polygonAlgebra a)
    (b : Fin 3 → Fin 3 → Fin m × (CutRing × CutRing))
    (hb : ∀ i, Function.Injective (SlotMap a m U (b i)))
    (hdis : ∀ i j, i ≠ j → Disjoint (Set.range (SlotMap a m U (b i)))
      (Set.range (SlotMap a m U (b j)))) :
    ∃ g ∈ polygonAlternatingGroup a m, ∀ (i : Fin 3) (x : U.val),
      g.val (SlotMap a m U (b 0) (i,x)) = SlotMap a m U (b 1) (i,x) := by
  let h := bankSlots_injective U b hb hdis
  refine ⟨slotHom U (bankSlots b) h bankPermutation,
    slotHom_alternating_mem U _ h bankPermutation_even,?_⟩
  intro i x
  have he (k : Fin 3) : SlotMap a m U (b k) (i,x) =
      SlotMap a m U (bankSlots b) (bankIndex (k,i),x) := by simp [SlotMap]
  rw [he 0,he 1]
  change slotPerm _ _ _ _ _ = _
  rw [slotPerm_apply,bankPermutation_apply,zero_add]

theorem slot_ranges_disjoint_of_tracks {a m n k : ℕ} (U : polygonAlgebra a)
    (s : Fin n → Fin m × (CutRing × CutRing))
    (t : Fin k → Fin m × (CutRing × CutRing))
    (h : ∀ i j, (s i).1 ≠ (t j).1) :
    Disjoint (Set.range (SlotMap a m U s)) (Set.range (SlotMap a m U t)) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨⟨i,x⟩,rfl⟩ ⟨⟨j,y⟩,he⟩
  exact h i j (congrArg Prod.fst he).symm

theorem fresh_nine_tracks {m : ℕ} (hm : 15 ≤ m) (s t : Fin 3 → Fin m) :
    ∃ e : Fin 9 ↪ Fin m, ∀ i j, e i ≠ s j ∧ e i ≠ t j := by
  classical
  let used := Finset.univ.image s ∪ Finset.univ.image t
  have hu : used.card ≤ 6 := by
    apply (Finset.card_union_le _ _).trans
    change _ + _ ≤ 3 + 3
    apply add_le_add <;> exact Finset.card_image_le.trans (by simp)
  have hc : 9 ≤ usedᶜ.card := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  have he : Nonempty (Fin 9 ↪ {x : Fin m // x ∈ usedᶜ}) := by
    rw [Function.Embedding.nonempty_iff_card_le,Fintype.card_fin,Fintype.card_coe]
    exact hc
  obtain ⟨e⟩ := he
  refine ⟨e.trans (Function.Embedding.subtype _),?_⟩
  intro i j
  have hn : (e i).val ∉ used := Finset.mem_compl.mp (e i).property
  constructor <;> intro heq <;> apply hn
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,heq.symm⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,heq.symm⟩)

theorem transport_three_slots {a m : ℕ} (hm : 15 ≤ m) (U : polygonAlgebra a)
    (s t : Fin 3 → Fin m × (CutRing × CutRing))
    (hs : Function.Injective (SlotMap a m U s))
    (ht : Function.Injective (SlotMap a m U t)) :
    ∃ g ∈ polygonAlternatingGroup a m, ∀ (i : Fin 3) (x : U.val),
      g.val (SlotMap a m U s (i,x)) = SlotMap a m U t (i,x) := by
  obtain ⟨e,he⟩ := fresh_nine_tracks hm (fun i => (s i).1) (fun i => (t i).1)
  let b : Fin 3 → Fin 3 → Fin m × (CutRing × CutRing) :=
    fun k i => (e (bankIndex (k,i)),0)
  have hb (k : Fin 3) : Function.Injective (SlotMap a m U (b k)) := by
    apply slots_injective_of_tracks
    intro i j hij
    exact congrArg Prod.snd (bankIndex.injective (e.injective hij))
  have hbb (k l : Fin 3) (hkl : k ≠ l) :
      Disjoint (Set.range (SlotMap a m U (b k))) (Set.range (SlotMap a m U (b l))) := by
    apply slot_ranges_disjoint_of_tracks
    intro i j hij
    exact hkl (congrArg Prod.fst (bankIndex.injective (e.injective hij)))
  have hsb (k : Fin 3) : Disjoint (Set.range (SlotMap a m U s))
      (Set.range (SlotMap a m U (b k))) := by
    apply slot_ranges_disjoint_of_tracks
    intro i j
    exact (he (bankIndex (k,j)) i).1.symm
  have htb (k : Fin 3) : Disjoint (Set.range (SlotMap a m U t))
      (Set.range (SlotMap a m U (b k))) := by
    apply slot_ranges_disjoint_of_tracks
    intro i j
    exact (he (bankIndex (k,j)) i).2.symm
  have hi₁ : ∀ i, Function.Injective (SlotMap a m U (![s,b 0,b 1] i)) := by
    intro i
    fin_cases i
    · exact hs
    · exact hb 0
    · exact hb 1
  have hd₁ : ∀ i j : Fin 3, i ≠ j →
      Disjoint (Set.range (SlotMap a m U (![s,b 0,b 1] i)))
        (Set.range (SlotMap a m U (![s,b 0,b 1] j))) := by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals first | exact False.elim (h rfl) | exact hsb 0 | exact hsb 1 |
      exact (hsb 0).symm | exact (hsb 1).symm | exact hbb 0 1 (by decide) |
      exact hbb 1 0 (by decide)
  obtain ⟨g₁,hg₁,hg₁act⟩ := transport_bank U ![s,b 0,b 1] hi₁ hd₁
  have hi₂ : ∀ i, Function.Injective (SlotMap a m U (![b 0,t,b 2] i)) := by
    intro i
    fin_cases i
    · exact hb 0
    · exact ht
    · exact hb 2
  have hd₂ : ∀ i j : Fin 3, i ≠ j →
      Disjoint (Set.range (SlotMap a m U (![b 0,t,b 2] i)))
        (Set.range (SlotMap a m U (![b 0,t,b 2] j))) := by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals first | exact False.elim (h rfl) | exact htb 0 | exact htb 2 |
      exact (htb 0).symm | exact (htb 2).symm | exact hbb 0 2 (by decide) |
      exact hbb 2 0 (by decide)
  obtain ⟨g₂,hg₂,hg₂act⟩ := transport_bank U ![b 0,t,b 2] hi₂ hd₂
  refine ⟨g₂*g₁,(polygonAlternatingGroup a m).mul_mem hg₂ hg₁,?_⟩
  intro i x
  change g₂.val (g₁.val _) = _
  have h₁ : g₁.val (SlotMap a m U s (i,x)) = SlotMap a m U (b 0) (i,x) := hg₁act i x
  have h₂ : g₂.val (SlotMap a m U (b 0) (i,x)) = SlotMap a m U t (i,x) := hg₂act i x
  rw [h₁,h₂]

end LocalDisplacement
end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ShiftedSlots
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section LocalDisplacement

theorem slotHom_supported {a m n : ℕ} (U : polygonAlgebra a)
    (s : Fin n → Fin m × (CutRing × CutRing)) (hs : Function.Injective (SlotMap a m U s))
    (σ : Equiv.Perm (Fin n)) :
    SupportedIn (slotHom U s hs σ).val (Set.range (SlotMap a m U s)) := by
  intro p hp
  exact slotPerm_apply_of_notMem U s hs σ hp

theorem slotHom_subcycle {a m n : ℕ} (U : polygonAlgebra a)
    (s : Fin n → Fin m × (CutRing × CutRing)) (hs : Function.Injective (SlotMap a m U s))
    (ι : Fin 3 ↪ Fin n) :
    slotHom U s hs (trackCycle ι) =
      slotHom U (s ∘ ι) (subslots_injective U s hs ι) (trackCycle (Function.Embedding.refl _)) := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  by_cases hp : p ∈ Set.range (SlotMap a m U (s ∘ ι))
  · obtain ⟨⟨i,x⟩,rfl⟩ := hp
    change slotPerm U s hs _ (SlotMap a m U s (ι i,x)) =
      slotPerm U (s ∘ ι) _ _ (SlotMap a m U (s ∘ ι) (i,x))
    rw [slotPerm_apply,slotPerm_apply,trackCycle_apply]
    have hi : trackCycle (Function.Embedding.refl (Fin 3)) i = i+1 :=
      trackCycle_apply (Function.Embedding.refl _) i
    rw [hi]
    rfl
  · rw [slotHom_supported U (s ∘ ι) _ _ p hp]
    by_cases hP : p ∈ Set.range (SlotMap a m U s)
    · obtain ⟨⟨j,x⟩,rfl⟩ := hP
      change slotPerm U s hs _ _ = _
      rw [slotPerm_apply]
      have hj : j ∉ Set.range ι := by
        rintro ⟨i,rfl⟩
        exact hp ⟨(i,x),rfl⟩
      rw [trackCycle_apply_of_notMem ι hj]
    · exact slotHom_supported U s hs _ p hP

open scoped commutatorElement in
theorem relative_normal_commutator_mem {G : Type*} [Group G]
    (N A : Subgroup G)
    (hN : ∀ n ∈ N, ∀ g ∈ A, g*n*g⁻¹ ∈ N)
    {n g : G} (hn : n ∈ N) (hg : g ∈ A) : ⁅n,g⁆ ∈ N := by
  have h := N.mul_mem hn (hN n⁻¹ (N.inv_mem hn) g hg)
  simpa only [commutatorElement_def,mul_assoc] using h

open scoped commutatorElement in

theorem displaced_five_slot_cycle_mem {a m : ℕ}
    (N : Subgroup (polygonFullGroup a m))
    (hN : ∀ n ∈ N, ∀ g ∈ polygonAlternatingGroup a m, g*n*g⁻¹ ∈ N)
    (n : polygonFullGroup a m) (hn : n ∈ N)
    (D : Set (TrackPoint a m)) (hD : Disjoint D (n.val '' D))
    (U : polygonAlgebra a) (hU : U.val.Nonempty)
    (s : Fin 5 → Fin m × (CutRing × CutRing)) (hs : Function.Injective (SlotMap a m U s))
    (hUD : Set.range (SlotMap a m U s) ⊆ D) :
    slotHom U s hs (trackCycle threeInFive) ∈ N := by
  let B := slotHom U s hs (trackCycle leftThreeInFive)
  let C := slotHom U s hs (trackCycle rightThreeInFive)
  have hB : B ∈ polygonAlternatingGroup a m :=
    Subgroup.subset_closure (slotHom_cycle_isThreeSlotCycle U hU s hs _)
  have hC : C ∈ polygonAlternatingGroup a m :=
    Subgroup.subset_closure (slotHom_cycle_isThreeSlotCycle U hU s hs _)
  have hBs : SupportedIn B.val D := (slotHom_supported U s hs _).mono hUD
  have hCs : SupportedIn C.val D := (slotHom_supported U s hs _).mono hUD
  have he : ⁅⁅n,B⁻¹⁆,C⁆ = ⁅B,C⁆ := by
    apply Subtype.ext
    change ⁅⁅n.val,B.val⁻¹⁆,C.val⁆ = ⁅B.val,C.val⁆
    simpa only [inv_inv] using supported_double_commutator n.val B.val⁻¹ C.val D
      (supported_inv hBs) hCs hD
  have hh := relative_normal_commutator_mem N _ hN
    (relative_normal_commutator_mem N _ hN hn ((polygonAlternatingGroup a m).inv_mem hB)) hC
  rw [he] at hh
  change ⁅slotHom U s hs (trackCycle leftThreeInFive),
    slotHom U s hs (trackCycle rightThreeInFive)⁆ ∈ N at hh
  rwa [← map_commutatorElement,five_cycle_commutator] at hh

theorem polygon_separates {a : ℕ} (p q : GenericSquare a) (hpq : p ≠ q) :
    ∃ U : polygonAlgebra a, p ∈ U.val ∧ q ∉ U.val := by
  have hs (j : Fin 4) (hl : cutForm a j p.val < cutForm a j q.val) :
      ∃ U : polygonAlgebra a, p ∈ U.val ∧ q ∉ U.val := by
    obtain ⟨c,hpc,hcq⟩ := exists_cut_between hl
    exact ⟨⟨halfPlane a j c,halfPlane_mem a j c⟩,hpc,not_lt.mpr hcq.le⟩
  have hr (j : Fin 4) (hl : cutForm a j q.val < cutForm a j p.val) :
      ∃ U : polygonAlgebra a, p ∈ U.val ∧ q ∉ U.val := by
    obtain ⟨c,hqc,hcp⟩ := exists_cut_between hl
    exact ⟨⟨(halfPlane a j c)ᶜ,BooleanSubalgebra.compl_mem (halfPlane_mem a j c)⟩,
      not_lt.mpr hcp.le,fun h => h hqc⟩
  by_cases hx : p.val.1 = q.val.1
  · have hy : p.val.2 ≠ q.val.2 := by
      intro h
      exact hpq (Subtype.ext (Prod.ext hx h))
    rcases lt_or_gt_of_ne hy with hy | hy
    · exact hs 1 hy
    · exact hr 1 hy
  · rcases lt_or_gt_of_ne hx with hx | hx
    · exact hs 0 hx
    · exact hr 0 hx

theorem exists_displaced_polygon {a m : ℕ} (n : polygonFullGroup a m) (hn : n ≠ 1) :
    ∃ (t : Fin m) (U : polygonAlgebra a), U.val.Nonempty ∧
      Disjoint {p : TrackPoint a m | p.1 = t ∧ p.2 ∈ U.val}
        (n.val '' {p : TrackPoint a m | p.1 = t ∧ p.2 ∈ U.val}) := by
  have hex : ∃ p, n.val p ≠ p := by
    by_contra! h
    apply hn
    apply Subtype.ext
    exact Equiv.ext h
  obtain ⟨p,hp⟩ := hex
  obtain ⟨cs,hcs,hcover⟩ := n.property
  obtain ⟨c,hc,hcp⟩ := hcover p
  have hscene : n.val p = (c.target,translate a c.shift p.2) := by
    have h := hcs c hc p.2 hcp.2
    simpa only [← hcp.1] using h
  by_cases htrack : c.target = c.source
  · have hneq : p.2 ≠ translate a c.shift p.2 := by
      intro h
      apply hp
      rw [hscene]
      exact Prod.ext (htrack.trans hcp.1.symm) h.symm
    obtain ⟨V,hpV,hqV⟩ := polygon_separates p.2 (translate a c.shift p.2) hneq
    let U : polygonAlgebra a :=
      ⟨c.domain.val ∩ V.val ∩ translate a c.shift ⁻¹' V.valᶜ,
       BooleanSubalgebra.inf_mem (BooleanSubalgebra.inf_mem c.domain.property V.property)
         (polygon_preimage_translate _ (BooleanSubalgebra.compl_mem V.property))⟩
    refine ⟨c.source,U,⟨p.2,⟨hcp.2,hpV⟩,hqV⟩,?_⟩
    apply Set.disjoint_left.mpr
    rintro z hz ⟨y,hy,rfl⟩
    have he : n.val y = (c.target,translate a c.shift y.2) := by
      simpa only [← hy.1] using hcs c hc y.2 hy.2.1.1
    rw [he] at hz
    exact hy.2.2 hz.2.1.2
  · refine ⟨c.source,c.domain,⟨p.2,hcp.2⟩,?_⟩
    apply Set.disjoint_left.mpr
    rintro z hz ⟨y,hy,rfl⟩
    have he : n.val y = (c.target,translate a c.shift y.2) := by
      simpa only [← hy.1] using hcs c hc y.2 hy.2
    rw [he] at hz
    exact htrack hz.1

private theorem slotMap_shifted {a m n : ℕ} {U V : polygonAlgebra a}
    (u : CutRing × CutRing) (hVU : V.val ⊆ (translatedPolygon u U).val)
    (s : Fin n → Fin m × (CutRing × CutRing)) (i : Fin n) (x : V.val) :
    SlotMap a m V (shiftedSlots u s) (i,x) =
      SlotMap a m U s (i,⟨translate a (-u) x.val,untranslate_mem u hVU x⟩) := by
  simp only [SlotMap,shiftedSlots,sub_eq_add_neg,translate_add]

private theorem shiftedSlots_injective {a m n : ℕ} {U V : polygonAlgebra a}
    (u : CutRing × CutRing) (hVU : V.val ⊆ (translatedPolygon u U).val)
    (s : Fin n → Fin m × (CutRing × CutRing))
    (hs : Function.Injective (SlotMap a m U s)) :
    Function.Injective (SlotMap a m V (shiftedSlots u s)) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  rw [slotMap_shifted u hVU,slotMap_shifted u hVU] at he
  have hh := hs he
  refine Prod.ext (congrArg (fun p : Fin n × U.val => p.1) hh) (Subtype.ext ?_)
  exact (translation a (-u)).injective (congrArg (fun p => p.2.val) hh)

theorem threeSlot_eq_slotHom {a m : ℕ} {g : polygonFullGroup a m}
    (hg : IsThreeSlotCycle g) :
    ∃ (U : polygonAlgebra a) (s : Fin 3 → Fin m × (CutRing × CutRing))
      (hs : Function.Injective (SlotMap a m U s)),
      g = slotHom U s hs (trackCycle (Function.Embedding.refl _)) := by
  obtain ⟨U,s,hU,hs,hact,hfix⟩ := hg
  refine ⟨U,s,hs,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro p
  by_cases hp : p ∈ Set.range (SlotMap a m U s)
  · obtain ⟨⟨i,x⟩,rfl⟩ := hp
    change g.val (SlotMap a m U s (i,x)) = slotPerm U s hs _ _
    rw [hact,slotPerm_apply]
    exact (congrArg (fun j => SlotMap a m U s (j,x))
      (trackCycle_apply (Function.Embedding.refl (Fin 3)) i)).symm
  · exact (hfix p hp).trans (slotPerm_apply_of_notMem U s hs _ hp).symm

theorem alternating_le_of_nontrivial_relative_normal {a m : ℕ} (hm : 15 ≤ m)
    (N : Subgroup (polygonFullGroup a m))
    (hN : ∀ n ∈ N, ∀ g ∈ polygonAlternatingGroup a m, g*n*g⁻¹ ∈ N)
    (n : polygonFullGroup a m) (hn : n ∈ N) (hne : n ≠ 1) :
    polygonAlternatingGroup a m ≤ N := by
  obtain ⟨t,U,hU,hdis⟩ := exists_displaced_polygon n hne
  obtain ⟨d,hd,hd1,s,hs,hD⟩ := five_slots_in_polygon U hU t
  obtain ⟨cover,hcover⟩ := smallSquare_finite_translated_cover a d hd hd1
  apply (Subgroup.closure_le _).mpr
  intro f hf
  obtain ⟨V,v,hv,rfl⟩ := threeSlot_eq_slotHom hf
  apply slotHom_of_finite_cover cover (fun u => translatedPolygon u (smallSquare a d))
    V v hv _ N
  · intro x _
    exact hcover x
  · intro u _ W hWV hWu
    by_cases hW : W.val.Nonempty
    · let s' := shiftedSlots u s
      have hs' : Function.Injective (SlotMap a m W s') := shiftedSlots_injective u hWu s hs
      have hD' : Set.range (SlotMap a m W s') ⊆ {p | p.1 = t ∧ p.2 ∈ U.val} := by
        rintro p ⟨⟨i,x⟩,rfl⟩
        rw [slotMap_shifted u hWu]
        exact hD ⟨_,rfl⟩
      have hlocal := displaced_five_slot_cycle_mem N hN n hn _ hdis W hW s' hs' hD'
      rw [slotHom_subcycle] at hlocal
      let targets := s' ∘ threeInFive
      have ht := subslots_injective W s' hs' threeInFive
      have hvW := SlotMap_injective_mono v hWV hv
      obtain ⟨g,hg,hgact⟩ := transport_three_slots hm W v targets hvW ht
      have heq := slotHom_conjugate W v targets hvW ht g hgact
        (trackCycle (Function.Embedding.refl (Fin 3)))
      have hc := hN _ hlocal g⁻¹ ((polygonAlternatingGroup a m).inv_mem hg)
      rw [← heq] at hc
      simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hc
    · rw [slotHom_empty W v _ _ (Set.not_nonempty_iff_eq_empty.mp hW)]
      exact N.one_mem

theorem polygonAlternatingGroup_simple (a m : ℕ) (hm : 15 ≤ m) :
    IsSimpleGroup (polygonAlternatingGroup a m) := by
  rw [Subgroup.isSimpleGroup_iff]
  have hinf := polygonAlternatingGroup_infinite a m (by omega)
  let : Infinite (polygonAlternatingGroup a m) := hinf
  refine ⟨(polygonAlternatingGroup a m).nontrivial_iff_ne_bot.mp inferInstance,?_⟩
  intro N hNA hnormal
  by_cases hN : N = ⊥
  · exact Or.inl hN
  · right
    apply le_antisymm hNA
    have hex : ∃ n ∈ N, n ≠ 1 := by
      by_contra! h
      exact hN ((Subgroup.eq_bot_iff_forall N).mpr h)
    obtain ⟨n,hn,hne⟩ := hex
    apply alternating_le_of_nontrivial_relative_normal hm N ?_ n hn hne
    intro x hx g hg
    have hh := hnormal.conj_mem (⟨x,hNA hx⟩ : polygonAlternatingGroup a m) hx
      (⟨g,hg⟩ : polygonAlternatingGroup a m)
    exact hh

end LocalDisplacement

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SeparatedAxisSectors
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section AxisCoherence

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

@[simp] theorem fullGeometricSector_bot {ι : Type*} [Finite ι] (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P) :
    B.fullGeometricSector hlarge P h ⊥ = 1 := by
  unfold fullGeometricSector
  have he : resolvedPolygonMask (primitiveTests (a := a) (r := r) P) (⊥ : polygonAlgebra a).val = ∅ := by
    ext ω
    simp [resolvedPolygonMask]
  rw [he,ActualLawfulTable.sector_empty]

@[simp] theorem axisSector_self (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (u : CutRing) :
    B.axisSector hlarge n g d k hk p (coordinateInterval a d u u) = 1 := by
  rw [coordinateInterval_self]
  exact B.fullGeometricSector_bot hlarge _ _

end InitialCoverSystem
end AxisCoherence

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_AxisCutSequences
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AxisCutSequences

namespace AxisCutSequence
variable {n K : ℕ} (D : AxisCutSequence n K)

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (g : B.CoordinateWindowLaw n) (d : Fin 2)

@[simp] theorem prefix_zero : D.prefixCopy B hlarge g d 0 = 1 := by
  simp only [prefixCopy,index_zero,InitialCoverSystem.axisSector_self]

end AxisCutSequence
end AxisCutSequences

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_SuccessfulLawCovariance
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section FiniteMixtureWeights
open Classical

theorem finiteUniformWeight_nonneg {G : Type*} (U : Finset G) (x : G) :
    0 ≤ finiteUniformWeight U x := by unfold finiteUniformWeight; split_ifs <;> positivity

theorem finiteUniformWeight_sum {G : Type*} (S U : Finset G) (hUS : U ⊆ S) (f : G → ℝ) :
    (∑x∈S,finiteUniformWeight U x*f x)=(∑x∈U,f x)/U.card := by
  calc
    _ = ∑x∈U,finiteUniformWeight U x*f x := by
      symm
      apply Finset.sum_subset hUS
      intro x hx hxU
      simp [finiteUniformWeight,hxU]
    _ = ∑x∈U,f x/(U.card:ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [finiteUniformWeight,hx,div_eq_mul_inv,mul_comm]
    _ = _ := by rw [Finset.sum_div]

theorem finite_uniform_mixture {X G : Type*} (T : Finset X) (w : X → ℝ) (U : X → Finset G)
    (hw : ∀x∈T,0 ≤ w x) (hmass : (∑x∈T,w x)=1) (hU : ∀x∈T,(U x).Nonempty) :
    ∃ (S : Finset G) (p : G → ℝ), (∀g,0 ≤ p g) ∧ (∀g∉S,p g=0) ∧ (∑g∈S,p g)=1 ∧
      ∀f : G → ℝ,(∑g∈S,p g*f g)=∑x∈T,w x*((∑g∈U x,f g)/(U x).card) := by
  let S := T.biUnion U
  let p := fun g => ∑x∈T,w x*finiteUniformWeight (U x) g
  have hcontains (x : X) (hx : x∈T) : U x ⊆ S := by
    intro g hg
    exact Finset.mem_biUnion.mpr ⟨x,hx,hg⟩
  have htest (f : G → ℝ) : (∑g∈S,p g*f g)=∑x∈T,w x*((∑g∈U x,f g)/(U x).card) := by
    simp only [p,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [mul_assoc]
    rw [←Finset.mul_sum,finiteUniformWeight_sum S (U x) (hcontains x hx)]
  refine ⟨S,p,fun g => Finset.sum_nonneg (fun x hx => mul_nonneg (hw x hx)
    (finiteUniformWeight_nonneg (U x) g)),?_,?_,htest⟩
  · intro g hg
    apply Finset.sum_eq_zero
    intro x hx
    have hgU : g∉U x := fun h => hg (hcontains x hx h)
    simp [finiteUniformWeight,hgU]
  · have hh := htest (fun _ => 1)
    simp only [mul_one,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
    rw [hh]
    calc
      (∑x∈T,w x*(((U x).card:ℝ)/(U x).card)) = ∑x∈T,w x := by
        apply Finset.sum_congr rfl
        intro x hx
        have hcard : ((U x).card:ℝ)≠0 := by exact_mod_cast (hU x hx).card_pos.ne'
        field_simp
      _ = 1 := hmass

end FiniteMixtureWeights

section FiniteTestReiter
open Classical Set

theorem sum_support_window {G : Type*} (S W : Finset G) (p f : G → ℝ)
    (hS : S ⊆ W) (hp : ∀x∉S,p x=0) :
    (∑x∈W,p x*f x)=∑x∈S,p x*f x := by
  symm
  apply Finset.sum_subset hS
  intro x hx hn
  simp [hp x hn]

theorem sum_translate_window {G : Type*} [Group G] (S W : Finset G) (p f : G → ℝ) (k : G)
    (hS : S.image (fun x => k*x) ⊆ W) (hp : ∀x∉S,p x=0) :
    (∑x∈W,p (k⁻¹*x)*f x)=∑x∈S,p x*f (k*x) := by
  calc
    _ = ∑x∈S.image (fun y => k*y),p (k⁻¹*x)*f x := by
      symm
      apply Finset.sum_subset hS
      intro x hx hn
      have hx' : k⁻¹*x∉S := by
        intro hh
        exact hn (Finset.mem_image.mpr ⟨k⁻¹*x,hh,by group⟩)
      simp [hp _ hx']
    _ = _ := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro x hx
        simp
      · intro x hx y hy he
        exact mul_left_cancel he

theorem finite_test_l1_bound {G : Type*} [Group G] (S W : Finset G) (p : G → ℝ) (k : G)
    (hS : S ⊆ W) (hkS : S.image (fun x => k*x) ⊆ W) (hp : ∀x∉S,p x=0)
    (δ : ℝ) (htest : ∀f : G → ℝ,(∀x,f x∈Icc (0:ℝ) 1) →
      |(∑x∈S,p x*f x)-(∑x∈S,p x*f (k*x))| ≤ δ) :
    (∑x∈W,|p (k⁻¹*x)-p x|) ≤ 2*δ := by
  let d := fun x => p (k⁻¹*x)-p x
  have hd (f : G → ℝ) (hf : ∀x,f x∈Icc (0:ℝ) 1) : |∑x∈W,d x*f x| ≤ δ := by
    simp only [d,sub_mul,Finset.sum_sub_distrib]
    rw [sum_translate_window S W p f k hkS hp,sum_support_window S W p f hS hp,abs_sub_comm]
    exact htest f hf
  let fpos := fun x => if 0 ≤ d x then (1:ℝ) else 0
  let fneg := fun x => if 0 ≤ d x then (0:ℝ) else 1
  have hfpos : ∀x,fpos x∈Icc (0:ℝ) 1 := by intro x; dsimp [fpos]; split_ifs <;> norm_num
  have hfneg : ∀x,fneg x∈Icc (0:ℝ) 1 := by intro x; dsimp [fneg]; split_ifs <;> norm_num
  have he : (∑x∈W,|d x|)=(∑x∈W,d x*fpos x)-(∑x∈W,d x*fneg x) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : 0 ≤ d x
    · simp [fpos,fneg,h,abs_of_nonneg h]
    · simp [fpos,fneg,h,abs_of_neg (lt_of_not_ge h)]
  change (∑x∈W,|d x|) ≤ _
  rw [he]
  linarith [(abs_le.mp (hd fpos hfpos)).2,(abs_le.mp (hd fneg hfneg)).1]

theorem finiteSupportReiter_of_finiteTestReiter {G : Type*} [Group G]
    (h : FiniteTestReiter G) : FiniteSupportReiter G := by
  intro K ε hε
  have hc : (0:ℝ)<2*(K.card:ℝ)+1 := by positivity
  let δ := ε/(2*(K.card:ℝ)+1)
  obtain ⟨S,p,hp,hs,hm,ht⟩ := h K δ (div_pos hε hc)
  refine ⟨S,p,hp,hs,hm,?_⟩
  have hbound : weightedVariation K S p ≤ (K.card:ℝ)*(2*δ) := by
    calc
      _ ≤ ∑k∈K,2*δ := by
        apply Finset.sum_le_sum
        intro k hk
        apply finite_test_l1_bound S (translationWindow K S) p k
          (Finset.subset_union_left) _ hs δ (ht k hk)
        intro x hx
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k,hk,hx⟩)
      _ = _ := by simp
  apply lt_of_le_of_lt hbound
  dsimp [δ]
  rw [←mul_assoc,←mul_div_assoc]
  apply (div_lt_iff₀ hc).mpr
  nlinarith

end FiniteTestReiter

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_SubgroupTestReiter
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SubgroupTestReiter
open Classical Set

theorem subgroupCoordinate_spec {G : Type*} [Group G] (H : Subgroup G) (x : G) :
    (subgroupCoordinate H x:G)*subgroupOrbitBase H x=x := (subgroupOrbitBase_spec H x).choose_spec

theorem subgroupCoordinate_mul {G : Type*} [Group G] (H : Subgroup G) (k : H) (x : G) :
    subgroupCoordinate H ((k:G)*x)=k*subgroupCoordinate H x := by
  have hb : subgroupOrbitBase H x=subgroupOrbitBase H ((k:G)*x) :=
    congrArg Quotient.out (Quotient.sound (s:=subgroupOrbitSetoid H) ⟨k,rfl⟩)
  apply Subtype.ext
  apply mul_right_cancel (b:=subgroupOrbitBase H ((k:G)*x))
  rw [subgroupCoordinate_spec]
  change (k:G)*x=((k:G)*(subgroupCoordinate H x:G))*subgroupOrbitBase H ((k:G)*x)
  rw [←hb,mul_assoc,subgroupCoordinate_spec]

theorem finite_weights_push {X Y : Type*} (S : Finset X) (p : X → ℝ) (π : X → Y)
    (hp : ∀x,0 ≤ p x) (hm : (∑x∈S,p x)=1) :
    ∃(T : Finset Y) (q : Y → ℝ),(∀y,0 ≤ q y) ∧ (∀y∉T,q y=0) ∧ (∑y∈T,q y)=1 ∧
      ∀f : Y → ℝ,(∑y∈T,q y*f y)=∑x∈S,p x*f (π x) := by
  obtain ⟨T,q,hq,hs,ht,havg⟩ := finite_uniform_mixture S p (fun x => {π x})
    (fun x _ => hp x) hm (fun _ _ => Finset.singleton_nonempty _)
  refine ⟨T,q,hq,hs,ht,?_⟩
  intro f
  simpa using havg f

theorem FiniteTestReiter.subgroup {G : Type*} [Group G] (h : FiniteTestReiter G)
    (H : Subgroup G) : FiniteTestReiter H := by
  intro K ε hε
  obtain ⟨S,p,hp,hs,hm,ht⟩ := h (K.image (fun k : H => (k:G))) ε hε
  obtain ⟨T,q,hq,hT,hM,havg⟩ := finite_weights_push S p (subgroupCoordinate H) hp hm
  refine ⟨T,q,hq,hT,hM,?_⟩
  intro k hk f hf
  rw [havg,havg]
  have hh := ht (k:G) (Finset.mem_image_of_mem (fun k : H => (k:G)) hk)
    (fun x => f (subgroupCoordinate H x)) (fun x => hf (subgroupCoordinate H x))
  simpa only [subgroupCoordinate_mul] using hh

end SubgroupTestReiter

section PolygonAmenability

theorem polygonAlternatingGroup_folner {a m : ℕ} (ha : 0 < a) :
    FolnerAmenable (polygonAlternatingGroup a m) :=
  folner_of_finite_reiter (finiteSupportReiter_of_finiteTestReiter
    ((polygonFullGroup_finiteTestReiter ha).subgroup (polygonAlternatingGroup a m)))

theorem polygon_infinite_simple_folner_oai {a m : ℕ} (ha : 0 < a) (hm : 15 ≤ m) :
    Infinite (polygonAlternatingGroup a m) ∧ IsSimpleGroup (polygonAlternatingGroup a m) ∧
    FolnerAmenable (polygonAlternatingGroup a m) :=
  ⟨polygonAlternatingGroup_infinite a m (by omega),polygonAlternatingGroup_simple a m hm,
    polygonAlternatingGroup_folner ha⟩

end PolygonAmenability

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.polygon_infinite_simple_folner_oai := @OAI.SimpleAmenable.polygon_infinite_simple_folner_oai
