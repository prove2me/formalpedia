-- Prove2me | solution 1 for ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq_all
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c76ed302-3c8b-55f6-b30e-ea524ddd6cd9

import Mathlib
import Theorems.Thm_ModularCurve_exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq_all

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

namespace MWgen

open ModularCurve

section CoefFG
open Pointwise
variable {K : Type} [Field K]

def CoefFG (a : LaurentSeries K) : Prop := ∃ C : Finset K, ∀ n : ℤ, a.coeff n ∈ Submodule.span ℤ (C : Set K)

theorem CoefFG.zero : CoefFG (0 : LaurentSeries K) := ⟨∅, fun n => by simp⟩

theorem CoefFG.add {a b : LaurentSeries K} (ha : CoefFG a) (hb : CoefFG b) : CoefFG (a + b) := by
  classical
  obtain ⟨C, hC⟩ := ha; obtain ⟨D, hD⟩ := hb
  refine ⟨C ∪ D, fun n => ?_⟩
  rw [HahnSeries.coeff_add, Finset.coe_union]
  exact Submodule.add_mem _ (Submodule.span_mono Set.subset_union_left (hC n)) (Submodule.span_mono Set.subset_union_right (hD n))

theorem CoefFG.neg {a : LaurentSeries K} (ha : CoefFG a) : CoefFG (-a) := by
  obtain ⟨C, hC⟩ := ha; exact ⟨C, fun n => by rw [HahnSeries.coeff_neg]; exact Submodule.neg_mem _ (hC n)⟩

theorem CoefFG.mul {a b : LaurentSeries K} (ha : CoefFG a) (hb : CoefFG b) : CoefFG (a * b) := by
  classical
  obtain ⟨C, hC⟩ := ha; obtain ⟨D, hD⟩ := hb
  refine ⟨C * D, fun n => ?_⟩
  rw [HahnSeries.coeff_mul, Finset.coe_mul, ← Submodule.span_mul_span]
  exact Submodule.sum_mem _ fun ij _ => Submodule.mul_mem_mul (hC _) (hD _)

theorem CoefFG.single (c : K) (k : ℤ) : CoefFG (HahnSeries.single k c : LaurentSeries K) := by
  classical
  refine ⟨{c}, fun n => ?_⟩
  rw [HahnSeries.coeff_single]
  split_ifs
  · exact Submodule.subset_span (by simp)
  · exact Submodule.zero_mem _

theorem CoefFG.algebraMap (c : K) : CoefFG (algebraMap K (LaurentSeries K) c) := by
  rw [ModularCurve.algebraMap_laurentSeries_eq_single]; exact CoefFG.single c 0

theorem CoefFG.intSeriesC (P : PowerSeries ℤ) : CoefFG (intSeriesC K P) := by
  classical
  refine ⟨{1}, fun n => ?_⟩

  have : ∃ z : ℤ, (ModularCurve.intSeriesC K P).coeff n = (z : K) := by
    show ∃ z : ℤ, ((PowerSeries.map (Int.castRingHom K) P : PowerSeries K) : LaurentSeries K).coeff n = (z : K)
    rw [PowerSeries.coeff_coe]
    split_ifs
    · exact ⟨0, by simp⟩
    · exact ⟨PowerSeries.coeff n.natAbs P, by rw [PowerSeries.coeff_map]; rfl⟩
  obtain ⟨z, hz⟩ := this
  rw [hz, Finset.coe_singleton, ← zsmul_one]
  exact Submodule.smul_mem _ z (Submodule.subset_span rfl)

theorem CoefFG.coeffMap {K' : Type} [Field K'] (τ : K →+* K') {a : LaurentSeries K} (ha : CoefFG a) : CoefFG (coeffMap τ a) := by
  classical
  obtain ⟨C, hC⟩ := ha
  refine ⟨C.image τ, fun n => ?_⟩
  rw [coeffMap_coeff, Finset.coe_image]
  exact Submodule.apply_mem_span_image_of_mem_span (τ.toAddMonoidHom.toIntLinearMap) (hC n)

end CoefFG
end MWgen

namespace MWgen
open ModularCurve

section QuotF
variable {K : Type} [Field K] (F : IntermediateField K (LaurentSeries K))

def IsQuotF (w : LaurentSeries K) : Prop :=
  ∃ a b : LaurentSeries K, a ∈ F ∧ b ∈ F ∧ CoefFG a ∧ CoefFG b ∧ b ≠ 0 ∧ w * b = a

variable {F}

theorem isQuotF_of_mem {w : LaurentSeries K} (hwF : w ∈ F) (hw : CoefFG w) : IsQuotF F w :=
  ⟨w, 1, hwF, one_mem F, hw, by simpa using (CoefFG.intSeriesC (K := K) 1), one_ne_zero, mul_one w⟩

theorem IsQuotF.add {w w' : LaurentSeries K} (h : IsQuotF F w) (h' : IsQuotF F w') : IsQuotF F (w + w') := by
  obtain ⟨a, b, haF, hbF, ha, hb, hb0, hw⟩ := h
  obtain ⟨a', b', haF', hbF', ha', hb', hb0', hw'⟩ := h'
  refine ⟨a * b' + a' * b, b * b', add_mem (mul_mem haF hbF') (mul_mem haF' hbF), mul_mem hbF hbF',
    (ha.mul hb').add (ha'.mul hb), hb.mul hb', mul_ne_zero hb0 hb0', ?_⟩
  rw [add_mul, ← mul_assoc, hw, mul_comm b b', ← mul_assoc, hw']

theorem IsQuotF.neg {w : LaurentSeries K} (h : IsQuotF F w) : IsQuotF F (-w) := by
  obtain ⟨a, b, haF, hbF, ha, hb, hb0, hw⟩ := h
  exact ⟨-a, b, neg_mem haF, hbF, ha.neg, hb, hb0, by rw [neg_mul, hw]⟩

theorem IsQuotF.mul {w w' : LaurentSeries K} (h : IsQuotF F w) (h' : IsQuotF F w') : IsQuotF F (w * w') := by
  obtain ⟨a, b, haF, hbF, ha, hb, hb0, hw⟩ := h
  obtain ⟨a', b', haF', hbF', ha', hb', hb0', hw'⟩ := h'
  refine ⟨a * a', b * b', mul_mem haF haF', mul_mem hbF hbF', ha.mul ha', hb.mul hb', mul_ne_zero hb0 hb0', ?_⟩
  calc w * w' * (b * b') = (w * b) * (w' * b') := by ring
    _ = a * a' := by rw [hw, hw']

theorem IsQuotF.inv {w : LaurentSeries K} (h : IsQuotF F w) : IsQuotF F w⁻¹ := by
  by_cases hw0 : w = 0
  · subst hw0; rw [inv_zero]; exact isQuotF_of_mem (zero_mem F) CoefFG.zero
  obtain ⟨a, b, haF, hbF, ha, hb, hb0, hw⟩ := h
  have ha0 : a ≠ 0 := by rw [← hw]; exact mul_ne_zero hw0 hb0
  refine ⟨b, a, hbF, haF, hb, ha, ha0, ?_⟩
  rw [← hw, ← mul_assoc, inv_mul_cancel₀ hw0, one_mul]

variable (F) in

def quotFSubfield : Subfield (LaurentSeries K) where
  carrier := {w | IsQuotF F w}
  mul_mem' := fun h h' => IsQuotF.mul h h'
  one_mem' := isQuotF_of_mem (one_mem F) (by simpa using (CoefFG.intSeriesC (K := K) 1))
  add_mem' := fun h h' => IsQuotF.add h h'
  zero_mem' := isQuotF_of_mem (zero_mem F) CoefFG.zero
  neg_mem' := fun h => IsQuotF.neg h
  inv_mem' := fun _ h => IsQuotF.inv h

theorem isQuotF_of_mem_adjoin {S : Set (LaurentSeries K)} (hS : ∀ w ∈ S, IsQuotF F w) {w : LaurentSeries K}
    (hw : w ∈ IntermediateField.adjoin K S) : IsQuotF F w := by
  have h : (IntermediateField.adjoin K S).toSubfield ≤ quotFSubfield F := by
    rw [IntermediateField.adjoin_toSubfield]
    apply Subfield.closure_le.mpr
    rintro x (⟨c, rfl⟩ | hx)
    · exact isQuotF_of_mem (algebraMap_mem F c) (CoefFG.algebraMap c)
    · exact hS x hx
  exact h hw

end QuotF

theorem coeffMap_injective {R S : Type} [CommRing R] [CommRing S] {τ : R →+* S} (hτ : Function.Injective τ) :
    Function.Injective (coeffMap τ) := by
  intro a b h
  ext n
  exact hτ (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

section ValMax
variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀]

theorem exists_coeff_valuation_max (v : Valuation K Γ₀) (hv : ∀ z : ℤ, v z ≤ 1) {a : LaurentSeries K}
    (ha : CoefFG a) (ha0 : a ≠ 0) : ∃ n₀ : ℤ, a.coeff n₀ ≠ 0 ∧ ∀ n, v (a.coeff n) ≤ v (a.coeff n₀) := by
  classical
  obtain ⟨C, hC⟩ := ha

  set N' : Submodule ℤ K := Submodule.span ℤ (Set.range a.coeff) with hN'
  have hN'le : N' ≤ Submodule.span ℤ (C : Set K) := Submodule.span_le.mpr (by rintro _ ⟨n, rfl⟩; exact hC n)
  have hfg : N'.FG := by
    haveI : Module.Finite ℤ ↥(Submodule.span ℤ (C : Set K)) := Module.Finite.span_of_finite ℤ C.finite_toSet
    haveI : IsNoetherian ℤ ↥(Submodule.span ℤ (C : Set K)) := isNoetherian_of_isNoetherianRing_of_finite ℤ _
    have h1 : (N'.comap (Submodule.span ℤ (C : Set K)).subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map (Submodule.span ℤ (C : Set K)).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hN'le] at h2
  obtain ⟨T, hTfin, hTspan⟩ := Submodule.fg_def.mp hfg

  have hT : ∀ t ∈ T, ∃ S : Finset K, (S : Set K) ⊆ Set.range a.coeff ∧ t ∈ Submodule.span ℤ (S : Set K) := by
    intro t ht
    have : t ∈ N' := by rw [← hTspan]; exact Submodule.subset_span ht
    exact Submodule.mem_span_finite_of_mem_span this
  choose S hS using hT
  let S₀ : Finset K := hTfin.toFinset.attach.biUnion fun t => S t.1 (hTfin.mem_toFinset.mp t.2)
  have hS₀sub : (S₀ : Set K) ⊆ Set.range a.coeff := by
    intro s hs
    simp only [S₀, Finset.coe_biUnion, Set.mem_iUnion] at hs
    obtain ⟨t, -, hst⟩ := hs
    exact (hS t.1 _).1 hst
  have hN'S₀ : N' ≤ Submodule.span ℤ (S₀ : Set K) := by
    rw [← hTspan]
    apply Submodule.span_le.mpr
    intro t ht
    have h := (hS t (by exact ht)).2
    refine Submodule.span_mono ?_ h
    intro s hs
    simp only [S₀, Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨⟨t, hTfin.mem_toFinset.mpr ht⟩, Finset.mem_attach _ _, hs⟩

  have hne : ∃ s ∈ S₀, s ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hbot : Submodule.span ℤ (S₀ : Set K) = ⊥ := by
      rw [Submodule.span_eq_bot]; exact fun s hs => hall s hs
    apply ha0
    ext n
    have : a.coeff n ∈ N' := Submodule.subset_span ⟨n, rfl⟩
    have := hN'S₀ this
    rw [hbot, Submodule.mem_bot] at this
    simpa using this
  obtain ⟨s₁, hs₁, hs₁0⟩ := hne
  obtain ⟨s₀, hs₀, hmax⟩ := Finset.exists_max_image S₀ v ⟨s₁, hs₁⟩
  obtain ⟨n₀, hn₀⟩ := hS₀sub hs₀
  refine ⟨n₀, ?_, ?_⟩
  · rw [hn₀]
    intro h0
    have : v s₁ ≤ v s₀ := hmax s₁ hs₁
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hs₁0 this
  · intro n
    rw [hn₀]
    have hmem : a.coeff n ∈ Submodule.span ℤ (S₀ : Set K) := hN'S₀ (Submodule.subset_span ⟨n, rfl⟩)
    refine Submodule.span_induction (p := fun x _ => v x ≤ v s₀) ?_ ?_ ?_ ?_ hmem
    · exact fun s hs => hmax s hs
    · show v 0 ≤ v s₀
      rw [map_zero]; exact zero_le'
    · intro x y _ _ hx hy
      show v (x + y) ≤ v s₀
      exact (v.map_add x y).trans (max_le hx hy)
    · intro z x _ hx
      show v (z • x) ≤ v s₀
      rw [zsmul_eq_mul, map_mul]
      exact (mul_le_of_le_one_left' (hv z)).trans hx

end ValMax
end MWgen

namespace MWgen

def liftSub {L : Type} [Field L] (A : ValuationSubring L) (s : LaurentSeries L) (h : ∀ n : ℤ, s.coeff n ∈ A) : LaurentSeries ↥A where
  coeff n := ⟨s.coeff n, h n⟩
  isPWO_support' := by
    have : (Function.support fun n : ℤ => (⟨s.coeff n, h n⟩ : ↥A)) = Function.support s.coeff := by
      ext n; simp only [Function.mem_support, Ne, Subtype.ext_iff]; rfl
    rw [this]; exact s.isPWO_support

theorem coeffMap_subtype_liftSub {L : Type} [Field L] (A : ValuationSubring L) (s : LaurentSeries L) (h : ∀ n : ℤ, s.coeff n ∈ A) :
    ModularCurve.coeffMap A.subtype (liftSub A s h) = s := by
  ext n; rfl

theorem liftSub_coeff {L : Type} [Field L] (A : ValuationSubring L) (s : LaurentSeries L) (h : ∀ n : ℤ, s.coeff n ∈ A) (n : ℤ) :
    ((liftSub A s h).coeff n : L) = s.coeff n := rfl
end MWgen

theorem solution
    (p N : ℕ) [Fact p.Prime] [NeZero N] (H : Subgroup (ZMod N)ˣ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (f : ↥(xHFunctionFieldBar N H)) (x y : LaurentSeries ↥A) (hy : coeffMap (IsLocalRing.residue ↥A) y ≠ 0)
    (hxy : ((f : ↥(xHFunctionFieldBar N H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) :
    ∃ x' y' : LaurentSeries ↥A,
      coeffMap A.subtype x' ∈ xHFunctionFieldBar N H ∧ coeffMap A.subtype y' ∈ xHFunctionFieldBar N H ∧
      coeffMap (IsLocalRing.residue ↥A) y' ≠ 0 ∧
      ((f : ↥(xHFunctionFieldBar N H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y' = coeffMap A.subtype x' := by
  classical

  set Kb := AlgebraicClosure ℚ with hKb
  have hT : ModularGroup.T ∈ CohCarrier.GammaH N H := ModularCurve.translation_mem_GammaH N H
  have hΓ : (1 : ℝ) ∈ ((CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]; exact AddSubgroup.mem_zmultiples 1

  have hFQ : xHFunctionField N H = ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H) := rfl

  have hgenQ : ∀ w ∈ ModularCurve.intFormRatiosC ℚ (CohCarrier.GammaH N H), MWgen.IsQuotF (xHFunctionField N H) w := by
    intro w hw
    obtain ⟨a, b, m, n, P, Q, haF, hbF, ha, hb, hb0, hwb⟩ :=
      ModularCurve.exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC ℚ (CohCarrier.GammaH N H) hΓ w hw
    refine ⟨a, b, haF, hbF, ?_, ?_, hb0, hwb⟩
    · rw [ha]; exact (MWgen.CoefFG.single 1 m).mul (MWgen.CoefFG.intSeriesC P)
    · rw [hb]; exact (MWgen.CoefFG.single 1 n).mul (MWgen.CoefFG.intSeriesC Q)
  have hallQ : ∀ u ∈ xHFunctionField N H, MWgen.IsQuotF (xHFunctionField N H) u := fun u hu =>
    MWgen.isQuotF_of_mem_adjoin hgenQ hu

  have hgen : ∀ w ∈ (⇑(coeffEmb Kb) '' (xHFunctionField N H : Set (LaurentSeries ℚ))), MWgen.IsQuotF (xHFunctionFieldBar N H) w := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨a, b, haF, hbF, ha, hb, hb0, hub⟩ := hallQ u hu
    refine ⟨coeffEmb Kb a, coeffEmb Kb b, coeffEmb_mem_laurentBaseChange Kb haF, coeffEmb_mem_laurentBaseChange Kb hbF,
      ha.coeffMap _, hb.coeffMap _, ?_, ?_⟩
    · exact fun h => hb0 (MWgen.coeffMap_injective (algebraMap ℚ Kb).injective (show coeffEmb Kb b = coeffEmb Kb 0 by rw [h, map_zero]))
    · rw [← map_mul, hub]
  have hf : MWgen.IsQuotF (xHFunctionFieldBar N H) ((f : ↥(xHFunctionFieldBar N H)) : LaurentSeries Kb) :=
    MWgen.isQuotF_of_mem_adjoin hgen f.2
  obtain ⟨a, b, haF, hbF, ha, hb, hb0, hfb⟩ := hf

  let v := A.valuation
  have hvA : ∀ t : Kb, v t ≤ 1 ↔ t ∈ A := fun t => A.valuation_le_one_iff t
  have hvZ : ∀ z : ℤ, v z ≤ 1 := fun z => (hvA z).mpr (intCast_mem A z)
  obtain ⟨n₀, hbn₀, hbmax⟩ := MWgen.exists_coeff_valuation_max v hvZ hb hb0
  set c : Kb := (b.coeff n₀)⁻¹ with hc
  set b' : LaurentSeries Kb := HahnSeries.single 0 c * b with hb'
  set a' : LaurentSeries Kb := HahnSeries.single 0 c * a with ha'
  have hb'coeff : ∀ n, b'.coeff n = c * b.coeff n := fun n => HahnSeries.coeff_single_zero_mul
  have ha'coeff : ∀ n, a'.coeff n = c * a.coeff n := fun n => HahnSeries.coeff_single_zero_mul
  have hb'int : ∀ n, b'.coeff n ∈ A := by
    intro n
    rw [hb'coeff, ← hvA, map_mul, hc, map_inv₀]
    have h0 : v (b.coeff n₀) ≠ 0 := by rw [Ne, map_eq_zero]; exact hbn₀
    calc (v (b.coeff n₀))⁻¹ * v (b.coeff n) ≤ (v (b.coeff n₀))⁻¹ * v (b.coeff n₀) := mul_le_mul_right (hbmax n) _
      _ = 1 := inv_mul_cancel₀ h0
  have hb'n₀ : b'.coeff n₀ = 1 := by rw [hb'coeff, hc, inv_mul_cancel₀ hbn₀]
  have hfb' : ((f : ↥(xHFunctionFieldBar N H)) : LaurentSeries Kb) * b' = a' := by
    rw [hb', ha', mul_left_comm, hfb]

  have hsingle : ∀ t : Kb, (HahnSeries.single 0 t : LaurentSeries Kb) ∈ xHFunctionFieldBar N H := fun t => by
    rw [← ModularCurve.algebraMap_laurentSeries_eq_single]; exact algebraMap_mem _ t
  have ha'F : a' ∈ xHFunctionFieldBar N H := mul_mem (hsingle c) haF
  have hb'F : b' ∈ xHFunctionFieldBar N H := mul_mem (hsingle c) hbF

  have ha'int : ∀ n, a'.coeff n ∈ A := by
    by_contra hnot
    push Not at hnot

    have ha'fg : MWgen.CoefFG a' := (MWgen.CoefFG.single c 0).mul ha
    have ha'0 : a' ≠ 0 := by obtain ⟨n, hn⟩ := hnot; intro h; rw [h] at hn; exact hn (by simp)
    obtain ⟨n₁, ha'n₁, ha'max⟩ := MWgen.exists_coeff_valuation_max v hvZ ha'fg ha'0
    have hbig : 1 < v (a'.coeff n₁) := by
      obtain ⟨n, hn⟩ := hnot
      rw [← hvA, not_le] at hn
      exact hn.trans_le (ha'max n)

    set d : Kb := (a'.coeff n₁)⁻¹ with hd
    have hvd : v d < 1 := by
      rw [hd, map_inv₀]; exact (inv_lt_one₀ (zero_lt_one.trans hbig)).mpr hbig
    have hdA : d ∈ A := (hvA d).mp hvd.le
    have hdres : IsLocalRing.residue ↥A ⟨d, hdA⟩ = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]; exact hvd
    set a'' : LaurentSeries Kb := HahnSeries.single 0 d * a' with ha''
    have ha''coeff : ∀ n, a''.coeff n = d * a'.coeff n := fun n => HahnSeries.coeff_single_zero_mul
    have ha''int : ∀ n, a''.coeff n ∈ A := by
      intro n
      rw [ha''coeff, ← hvA, map_mul, hd, map_inv₀]
      have h0 : v (a'.coeff n₁) ≠ 0 := by rw [Ne, map_eq_zero]; exact ha'n₁
      calc (v (a'.coeff n₁))⁻¹ * v (a'.coeff n) ≤ (v (a'.coeff n₁))⁻¹ * v (a'.coeff n₁) := mul_le_mul_right (ha'max n) _
        _ = 1 := inv_mul_cancel₀ h0
    have ha''n₁ : a''.coeff n₁ = 1 := by rw [ha''coeff, hd, inv_mul_cancel₀ ha'n₁]

    have hrel : a'' * coeffMap A.subtype y = HahnSeries.single 0 d * (b' * coeffMap A.subtype x) := by
      rw [ha'', ← hfb', ← hxy]; ring
    let A'' := MWgen.liftSub A a'' ha''int
    let B' := MWgen.liftSub A b' hb'int
    have hrelA : A'' * y = HahnSeries.single 0 (⟨d, hdA⟩ : ↥A) * (B' * x) := by
      apply MWgen.coeffMap_injective (τ := A.subtype) Subtype.val_injective
      rw [map_mul, map_mul, map_mul, MWgen.coeffMap_subtype_liftSub, MWgen.coeffMap_subtype_liftSub, coeffMap_single]
      exact hrel
    have hres := congrArg (coeffMap (IsLocalRing.residue ↥A)) hrelA
    rw [map_mul, map_mul, map_mul, coeffMap_single, hdres, HahnSeries.single_eq_zero, zero_mul] at hres
    have hA''res : coeffMap (IsLocalRing.residue ↥A) A'' ≠ 0 := by
      intro h0
      have := congrArg (fun s => s.coeff n₁) h0
      simp only [coeffMap_coeff, HahnSeries.coeff_zero] at this
      have h1 : (A''.coeff n₁) = 1 := Subtype.ext (by rw [MWgen.liftSub_coeff]; exact ha''n₁)
      rw [h1, map_one] at this
      exact one_ne_zero this
    exact mul_ne_zero hA''res hy hres

  refine ⟨MWgen.liftSub A a' ha'int, MWgen.liftSub A b' hb'int, ?_, ?_, ?_, ?_⟩
  · rw [MWgen.coeffMap_subtype_liftSub]; exact ha'F
  · rw [MWgen.coeffMap_subtype_liftSub]; exact hb'F
  · intro h0
    have := congrArg (fun s => s.coeff n₀) h0
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at this
    have h1 : ((MWgen.liftSub A b' hb'int).coeff n₀) = 1 := Subtype.ext (by rw [MWgen.liftSub_coeff]; exact hb'n₀)
    rw [h1, map_one] at this
    exact one_ne_zero this
  · rw [MWgen.coeffMap_subtype_liftSub, MWgen.coeffMap_subtype_liftSub]; exact hfb'

end S_ModularCurve_exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq_all
end P2MW
export P2MW.S_ModularCurve_exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq_all (solution)
