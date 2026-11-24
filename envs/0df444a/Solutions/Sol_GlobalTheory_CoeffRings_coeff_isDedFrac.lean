-- Prove2me | solution 1 for GlobalTheory.CoeffRings.coeff_isDedFrac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:35.042591+00:00
-- url     : https://prove2.me/submissions/f76a58a1-5add-41e0-a5f6-e214e4609f9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDiscreteValuationRingAndFiniteResidueFieldValu
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_SqrtNegDiscMemCoeffField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoefficientFieldIntegersDedekindFractionField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
namespace GlobalTheory.CoeffRings
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem isIntegral_one_add_rt0_div_two (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    IsIntegral ℤ ((1 + H.rt0) / 2) := by
  have hd : H.d % 16 = 7 := H.2
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 4 * k = H.d + 1 := ⟨(H.d + 1) / 4, by omega⟩
  have hkC : (4 : ℂ) * k = H.d + 1 := by exact_mod_cast hk
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k : ℤ), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_natCast, eq_intCast, Int.cast_natCast]
  linear_combination (1 / 4 : ℂ) * H.sqrt_neg_disc_sq + (1 / 4 : ℂ) * hkC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem exists_isInc_of_le_range {R : Type} [CommRing R] (g : R →+* ℂ)
    (hg : Function.Injective g) (S : Subring ℂ) (hS : S ≤ g.range) :
    ∃ b : S →+* R, _root_.GlobalTheory.Models.IsInc S.subtype g b := by
  let e : R ≃+* g.range := RingEquiv.ofBijective g.rangeRestrict
    ⟨fun a b h => hg (congrArg Subtype.val h), g.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (Subring.inclusion hS), fun x => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hS x.2⟩)
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem natCast_inv_mem_of_coprime (W : ValuationSubring ℂ) {p n : ℕ}
    (hpW : (p : ℂ) ∈ W.nonunits) (hn : n.Coprime p) : (n : ℂ)⁻¹ ∈ W := by
  rw [ValuationSubring.mem_nonunits_iff] at hpW
  have hle : ∀ m : ℤ, W.valuation (m : ℂ) ≤ 1 := fun m => by
    simpa using W.valuation_le_one (m : W)
  have hn1 : W.valuation (n : ℂ) = 1 := by
    refine le_antisymm (by simpa using hle n) (not_lt.mp fun hlt => ?_)
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hn
    have huvC : (u : ℂ) * n + v * p = 1 := by exact_mod_cast huv
    have h1 : W.valuation ((u : ℂ) * n) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle u)) hlt
    have h2 : W.valuation ((v : ℂ) * p) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle v)) hpW
    have := Valuation.map_add_lt _ h1 h2
    rw [huvC, map_one] at this
    exact lt_irrefl _ this
  exact W.mem_of_valuation_le_one _ (by rw [map_inv₀, hn1, inv_one])
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem mem_valuationSubring_of_isIntegral_moduli {K : Type} [Field K] (V : ValuationSubring K)
    {x : K} (hx : IsIntegral ℤ x) : x ∈ V := by
  have hV : IsIntegral V x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hV
  rw [← hy]
  exact y.2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem isDedekindDomain_valuationSubring_of_not_isUnit_natCast {K : Type} [Field K] [NumberField K]
    (V : ValuationSubring K) (p : ℕ) (hp : p ≠ 0) (hpV : ¬ IsUnit (p : V)) :
    IsDedekindDomain V := by
  let f : 𝓞 K →+* V := (algebraMap (𝓞 K) K).codRestrict V.toSubring
    (fun x => mem_valuationSubring_of_isIntegral_moduli V (RingOfIntegers.isIntegral_coe x))
  letI : Algebra (𝓞 K) V := f.toAlgebra
  have hcoe : ∀ x : 𝓞 K, ((algebraMap (𝓞 K) V x : V) : K) = algebraMap (𝓞 K) K x := fun _ => rfl
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal V).comap (algebraMap (𝓞 K) V)
  have hM : P.primeCompl ≤ nonZeroDivisors (𝓞 K) := by
    intro s hs
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rintro rfl
    exact hs P.zero_mem
  have hpP : ((p : 𝓞 K)) ∈ P := by
    show algebraMap (𝓞 K) V p ∈ IsLocalRing.maximalIdeal V
    rw [map_natCast]
    exact hpV
  have hP : P ≠ ⊥ := by
    intro h
    have : ((p : 𝓞 K)) = 0 := by simpa [h] using hpP
    exact hp (by exact_mod_cast this)
  have hinj : Function.Injective (algebraMap (𝓞 K) V) := by
    intro a b h
    apply RingOfIntegers.coe_injective
    have := congrArg Subtype.val h
    simpa [hcoe] using this
  haveI : IsLocalization P.primeCompl V :=
    { map_units := by
        rintro ⟨s, hs⟩
        by_contra h
        exact hs h
      surj := by
        intro v
        obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (v : K)
        have hb0 : algebraMap (𝓞 K) K b ≠ 0 := by
          intro h0
          exact nonZeroDivisors.ne_zero hb
            (by exact_mod_cast (IsFractionRing.injective (𝓞 K) K) (h0.trans (map_zero _).symm))
        let Dp := Localization.AtPrime P
        haveI : IsDiscreteValuationRing Dp :=
          IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hP Dp
        have hDinj : Function.Injective (algebraMap (𝓞 K) Dp) := IsLocalization.injective Dp hM
        obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap (𝓞 K) Dp a) (algebraMap (𝓞 K) Dp b)
        obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
        have hspec := IsLocalization.mk'_spec Dp x s
        have key : ∀ u w : 𝓞 K,
            algebraMap (𝓞 K) Dp u * IsLocalization.mk' Dp x s = algebraMap (𝓞 K) Dp w →
            u * x = w * s := by
          intro u w h
          apply hDinj
          rw [map_mul, map_mul, ← h, ← hspec, _root_.mul_assoc]
        rcases hc with hc | hc
        · have h1 := key a b hc
          by_cases hx : x ∈ P
          · exfalso
            apply s.2
            show algebraMap (𝓞 K) V s ∈ IsLocalRing.maximalIdeal V
            have hsv : algebraMap (𝓞 K) V s = v * algebraMap (𝓞 K) V x := by
              apply Subtype.ext
              show algebraMap (𝓞 K) K s = (v : K) * algebraMap (𝓞 K) K x
              rw [← hab, div_mul_eq_mul_div, eq_div_iff hb0]
              rw [← map_mul, ← map_mul, h1, mul_comm]
            rw [hsv]
            exact Ideal.mul_mem_left _ _ hx
          · refine ⟨(s, ⟨x, hx⟩), ?_⟩
            apply Subtype.ext
            show (v : K) * algebraMap (𝓞 K) K x = algebraMap (𝓞 K) K s
            rw [← hab, div_mul_eq_mul_div, div_eq_iff hb0, ← map_mul, ← map_mul, h1, mul_comm]
        · have h1 := key b a hc
          refine ⟨(x, s), ?_⟩
          apply Subtype.ext
          show (v : K) * algebraMap (𝓞 K) K s = algebraMap (𝓞 K) K x
          rw [← hab, div_mul_eq_mul_div, div_eq_iff hb0, ← map_mul, ← map_mul, ← h1, mul_comm]
      exists_of_eq := by
        intro x y h
        exact ⟨1, by rw [hinj h]⟩ }
  exact IsLocalization.isDedekindDomain (𝓞 K) hM V
end GlobalTheory.CoeffRings
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory GlobalTheory.CoeffRings
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct Pointwise
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.CoeffRings
namespace _root_.GlobalTheory.CoeffRings
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), _root_.GlobalTheory.Models.IsDedFrac (algebraMap (𝓞 c.F) c.F) ∧ Algebra.FiniteType ℤ (𝓞 c.F) ∧ (∀ A : ℕ, A ∣ l.A → ∃ b : _root_.GlobalTheory.Models.RZ H 1 A →+* 𝓞 c.F, _root_.GlobalTheory.Models.IsInc (_root_.GlobalTheory.Models.RZ H 1 A).subtype (c.F.val.toRingHom.comp (algebraMap (𝓞 c.F) c.F)) b) ∧ ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → _root_.GlobalTheory.Models.IsDedFrac (c.V W).subtype ∧ (∀ n : ℕ, n.Coprime p → IsUnit (n : c.V W)) ∧ ∀ S A : ℕ, S.Coprime p → 0 < A → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A ∈ c.F → ∃ b : _root_.GlobalTheory.Models.RZ H S A →+* c.V W, _root_.GlobalTheory.Models.IsInc (_root_.GlobalTheory.Models.RZ H S A).subtype (c.F.val.toRingHom.comp (c.V W).subtype) b := by
  intro E _ _ _ H l c
  haveI : FiniteDimensional ℚ c.F := c.2
  haveI : NumberField c.F := ⟨⟩
  have hw : IsIntegral ℤ ((1 + H.rt0) / 2) := isIntegral_one_add_rt0_div_two H
  have hnatF : ∀ n : ℕ, (n : ℂ) ∈ c.F := fun n => natCast_mem c.F n
  have hwF : (1 + H.rt0) / 2 ∈ c.F :=
    div_mem (add_mem (one_mem _) (_root_.GlobalTheory.HostModel.sqrtNegDisc_mem_coeffField c)) (by simpa using hnatF 2)
  have hintF : ∀ {x : ℂ} (hx : x ∈ c.F), IsIntegral ℤ x → IsIntegral ℤ (⟨x, hx⟩ : c.F) :=
    fun hx h => (isIntegral_algHom_iff c.F.val.toRingHom.toIntAlgHom Subtype.val_injective).mp h
  refine ⟨?_, inferInstance, ?_, ?_⟩
  · refine ⟨⟨inferInstance, inferInstance⟩, inferInstance, ?_⟩
    have h : IsFractionRing (𝓞 c.F) c.F := inferInstance
    exact h
  · intro A hA
    have hApos : 0 < A := Nat.pos_of_dvd_of_pos hA l.A_pos
    have hzF : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A ∈ c.F := by
      obtain ⟨k, hk⟩ := _root_.GlobalTheory.LevelExist.zeta_eq_pow_of_dvd l.A_pos hA
      rw [hk]
      exact pow_mem (_root_.GlobalTheory.HostModel.zeta_A_mem_coeff c) k
    have hz : IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A) := (_root_.GlobalTheory.HostModel.isPrimitiveRoot_zeta hApos).isIntegral hApos
    refine exists_isInc_of_le_range _
      (fun a b h => RingOfIntegers.coe_injective (Subtype.val_injective h)) _ ?_
    unfold _root_.GlobalTheory.Models.RZ
    rw [Subring.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨⟨⟨_, hwF⟩, hintF hwF hw⟩, rfl⟩
    · exact ⟨1, by simp⟩
    · exact ⟨⟨⟨_, hzF⟩, hintF hzF hz⟩, rfl⟩
  · intro p W hp hpW
    have memV : ∀ x : c.F, x ∈ c.V W ↔ (x : ℂ) ∈ W := fun x => by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.V
      exact ValuationSubring.mem_comap
    have hunit : ∀ n : ℕ, n.Coprime p → IsUnit (n : c.V W) := by
      intro n hn
      have hinvW := natCast_inv_mem_of_coprime W hpW hn
      have hn0 : (n : ℂ) ≠ 0 := by
        norm_cast
        rintro rfl
        exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hn)
      have hnF : (n : ℂ)⁻¹ ∈ c.F := inv_mem (hnatF n)
      refine IsUnit.of_mul_eq_one (a := (n : c.V W)) ⟨⟨_, hnF⟩, (memV _).mpr hinvW⟩ ?_
      apply Subtype.ext
      apply Subtype.ext
      simp [hn0]
    refine ⟨?_, hunit, ?_⟩
    · have hpV : ¬ IsUnit (p : c.V W) := by
        rintro hu
        obtain ⟨b, hb⟩ := hu.exists_right_inv
        have hbC : (p : ℂ) * ((b : c.F) : ℂ) = 1 := by
          have := congrArg (fun y : c.V W => ((y : c.F) : ℂ)) hb
          simpa using this
        rw [ValuationSubring.mem_nonunits_iff] at hpW
        have hbW : W.valuation ((b : c.F) : ℂ) ≤ 1 :=
          W.valuation_le_one ⟨_, (memV _).mp b.2⟩
        have := lt_of_le_of_lt (mul_le_of_le_one_right' hbW) hpW
        rw [← map_mul, hbC, map_one] at this
        exact lt_irrefl _ this
      have hD := isDedekindDomain_valuationSubring_of_not_isUnit_natCast (c.V W) p hp.ne_zero hpV
      refine ⟨⟨inferInstance, hD⟩, ⟨fun a b h => by exact_mod_cast congrArg Subtype.val h⟩, ?_⟩
      have h : IsFractionRing (c.V W) c.F := inferInstance
      exact h
    · intro S A hS hA hzF
      have hz : IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A) := (_root_.GlobalTheory.HostModel.isPrimitiveRoot_zeta hA).isIntegral hA
      have hSF : (S : ℂ)⁻¹ ∈ c.F := inv_mem (hnatF S)
      refine exists_isInc_of_le_range _
        (fun a b h => Subtype.val_injective (Subtype.val_injective h)) _ ?_
      unfold _root_.GlobalTheory.Models.RZ
      rw [Subring.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨⟨⟨_, hwF⟩, (memV _).mpr (mem_valuationSubring_of_isIntegral_moduli W hw)⟩, rfl⟩
      · exact ⟨⟨⟨_, hSF⟩, (memV _).mpr (natCast_inv_mem_of_coprime W hpW hS)⟩, rfl⟩
      · exact ⟨⟨⟨_, hzF⟩, (memV _).mpr (mem_valuationSubring_of_isIntegral_moduli W hz)⟩, rfl⟩
end _root_.GlobalTheory.CoeffRings
end GlobalTheory.CoeffRings
