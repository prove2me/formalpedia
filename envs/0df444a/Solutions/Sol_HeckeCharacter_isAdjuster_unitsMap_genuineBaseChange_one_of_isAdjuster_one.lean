-- Prove2me | solution 1 for HeckeCharacter.isAdjuster_unitsMap_genuineBaseChange_one_of_isAdjuster_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/3cff48ec-26df-5773-86a8-3c22fa2aca22

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_isAdjuster_unitsMap_genuineBaseChange_one_of_isAdjuster_one

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin
open scoped IsMulCommutative

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 160000
set_option Elab.async false
set_option maxSynthPendingDepth 3

namespace P2mS25BADJ

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors

noncomputable section

section generic
variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]

include K L in
omit [IsDedekindDomain A] [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
theorem faithfulSMul_AB : FaithfulSMul A B :=
  (faithfulSMul_iff_algebraMap_injective A B).2 (algebraMap_injective_of_field_isFractionRing A B K L)

include K in

theorem count_coe_map (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) :
    FractionalIdeal.count L w ((v.asIdeal.map (algebraMap A B) : Ideal B) : FractionalIdeal B⁰ L) =
      (v.asIdeal.ramificationIdx' w.asIdeal : ℤ) * (if w.asIdeal.under A = v.asIdeal then 1 else 0) := by
  classical
  haveI : FaithfulSMul A B := faithfulSMul_AB A K L B
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have hne : ∀ P ∈ (v.asIdeal.primesOver B).toFinset, P ≠ ⊥ := fun P hP =>
    Ideal.ne_bot_of_mem_primesOver v.ne_bot (Set.mem_toFinset.1 hP)
  have hcoe : ((v.asIdeal.map (algebraMap A B) : Ideal B) : FractionalIdeal B⁰ L) =
      ∏ P ∈ (v.asIdeal.primesOver B).toFinset, (P : FractionalIdeal B⁰ L) ^ v.asIdeal.ramificationIdx' P := by
    rw [Ideal.map_algebraMap_eq_finsetProd_pow (R := B) (p := v.asIdeal) v.ne_bot]
    exact (map_prod (FractionalIdeal.coeIdealHom B⁰ L) _ _).trans (Finset.prod_congr rfl fun P hP => by
      obtain ⟨h1, h2⟩ := Set.mem_toFinset.1 hP
      rw [map_pow, Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]; rfl)
  rw [hcoe, FractionalIdeal.count_prod]
  ·
    have hterm : ∀ P ∈ (v.asIdeal.primesOver B).toFinset,
        FractionalIdeal.count L w ((P : FractionalIdeal B⁰ L) ^ v.asIdeal.ramificationIdx' P) =
          (v.asIdeal.ramificationIdx' P : ℤ) * (if P = w.asIdeal then 1 else 0) := by
      intro P hP
      have hP' := Set.mem_toFinset.1 hP
      let wP : HeightOneSpectrum B := ⟨P, hP'.1, hne P hP⟩
      rw [FractionalIdeal.count_pow, show (P : FractionalIdeal B⁰ L) = (wP.asIdeal : FractionalIdeal B⁰ L) from rfl]
      by_cases h : P = w.asIdeal
      · have : wP = w := HeightOneSpectrum.ext h
        rw [this, FractionalIdeal.count_self, if_pos h]
      · have : wP ≠ w := fun h' => h (congrArg HeightOneSpectrum.asIdeal h')
        rw [FractionalIdeal.count_maximal_coprime L w this, if_neg h]
    rw [Finset.sum_congr rfl hterm]
    by_cases hw : w.asIdeal.under A = v.asIdeal
    · have hmem : w.asIdeal ∈ (v.asIdeal.primesOver B).toFinset :=
        Set.mem_toFinset.2 ⟨w.isPrime, ⟨hw.symm⟩⟩
      rw [Finset.sum_eq_single_of_mem w.asIdeal hmem (fun P _ hPw => by rw [if_neg hPw, mul_zero]), if_pos rfl, if_pos hw]
    · rw [if_neg hw, mul_zero]
      refine Finset.sum_eq_zero fun P hP => ?_
      have hP' := Set.mem_toFinset.1 hP
      have : P ≠ w.asIdeal := fun h => hw (by rw [← h]; exact hP'.2.over.symm)
      rw [if_neg this, mul_zero]
  · intro P hP
    exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr (hne P hP))

abbrev nE (𝔣 : Ideal A) (v : HeightOneSpectrum A) : ℕ := (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors

include K in
theorem count_coe_map_ideal (𝔣 : Ideal A) (h𝔣 : 𝔣 ≠ ⊥) (w : HeightOneSpectrum B) :
    FractionalIdeal.count L w ((𝔣.map (algebraMap A B) : Ideal B) : FractionalIdeal B⁰ L) =
      (((w.under A).asIdeal.ramificationIdx' w.asIdeal * nE A 𝔣 (w.under A) : ℕ) : ℤ) := by
  classical
  haveI : FaithfulSMul A B := faithfulSMul_AB A K L B
  have hfac : ∏ᶠ v : HeightOneSpectrum A, v.maxPowDividing 𝔣 = 𝔣 := Ideal.finprod_heightOneSpectrum_factorization h𝔣
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum A => v.maxPowDividing 𝔣).Finite := Ideal.finite_mulSupport h𝔣
  set T := hsupp.toFinset with hT
  have hprod : 𝔣 = ∏ v ∈ T, v.asIdeal ^ nE A 𝔣 v := by
    have h1 : ∏ᶠ v : HeightOneSpectrum A, v.maxPowDividing 𝔣 = ∏ v ∈ T, v.maxPowDividing 𝔣 :=
      finprod_eq_prod_of_mulSupport_subset _ (by simp [hT])
    rw [h1] at hfac
    exact hfac.symm
  have hmap : ((𝔣.map (algebraMap A B) : Ideal B) : FractionalIdeal B⁰ L) =
      ∏ v ∈ T, ((v.asIdeal.map (algebraMap A B) : Ideal B) : FractionalIdeal B⁰ L) ^ nE A 𝔣 v := by
    conv_lhs => rw [hprod]
    rw [show Ideal.map (algebraMap A B) (∏ v ∈ T, v.asIdeal ^ nE A 𝔣 v) = Ideal.mapHom (algebraMap A B) (∏ v ∈ T, v.asIdeal ^ nE A 𝔣 v) from rfl,
      map_prod]
    rw [show ((∏ v ∈ T, Ideal.mapHom (algebraMap A B) (v.asIdeal ^ nE A 𝔣 v) : Ideal B) : FractionalIdeal B⁰ L) =
      FractionalIdeal.coeIdealHom B⁰ L (∏ v ∈ T, Ideal.mapHom (algebraMap A B) (v.asIdeal ^ nE A 𝔣 v)) from rfl, map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_pow, map_pow]
    rfl
  have hne : ∀ v ∈ T, ((v.asIdeal.map (algebraMap A B) : Ideal B) : FractionalIdeal B⁰ L) ^ nE A 𝔣 v ≠ 0 := fun v _ =>
    pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr (Ideal.map_ne_bot_of_ne_bot v.ne_bot))
  rw [hmap, FractionalIdeal.count_prod L w _ _ hne]
  simp_rw [FractionalIdeal.count_pow, count_coe_map A K L B]
  have key : ∀ v : HeightOneSpectrum A, (w.asIdeal.under A = v.asIdeal) ↔ w.under A = v := fun v =>
    ⟨fun h => HeightOneSpectrum.ext h, fun h => by rw [← h]; rfl⟩
  by_cases hmem : w.under A ∈ T
  · rw [Finset.sum_eq_single_of_mem (w.under A) hmem]
    · rw [if_pos (show w.asIdeal.under A = (w.under A).asIdeal from rfl), mul_one]
      push_cast
      ring
    · intro v _ hv
      rw [if_neg (fun h => hv ((key v).1 h).symm), mul_zero, mul_zero]
  · have h0 : nE A 𝔣 (w.under A) = 0 := by
      by_contra h
      apply hmem
      rw [hT, Set.Finite.mem_toFinset, Function.mem_mulSupport]
      change (w.under A).asIdeal ^ nE A 𝔣 (w.under A) ≠ 1
      rw [Ideal.one_eq_top]
      intro htop
      have hlt : (w.under A).asIdeal ^ nE A 𝔣 (w.under A) ≤ (w.under A).asIdeal := Ideal.pow_le_self h
      rw [htop, top_le_iff] at hlt
      exact (w.under A).isPrime.ne_top hlt
    rw [h0, mul_zero, Nat.cast_zero]
    refine (Finset.sum_eq_zero fun v hv => ?_)
    by_cases hvw : w.asIdeal.under A = v.asIdeal
    · exact absurd (((key v).1 hvw) ▸ hv) hmem
    · rw [if_neg hvw, mul_zero, mul_zero]

end generic

section main

open M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin M4aHerbrand.ArchSemilocal
open scoped IsMulCommutative NumberField.LiesOver TensorProduct

variable (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]

lemma mul_map_one_inv {K : Type*} [Field K] [NumberField K] (u : (AdeleRing (𝓞 K) K)ˣ) :
    u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) 1)⁻¹ = u := by
  rw [map_one, inv_one, mul_one]

lemma genuineβ_fst_apply (x : AdeleRing (𝓞 E) E) (w : InfinitePlace F) :
    haveI : w.1.LiesOver (w.comap (algebraMap E F)).1 := liesOver_of_comap_eq rfl
    ((genuineBaseChange E F).β x).1 w =
      algebraMap ((w.comap (algebraMap E F)).Completion) w.Completion (x.1 (w.comap (algebraMap E F))) := by
  haveI : w.1.LiesOver (w.comap (algebraMap E F)).1 := liesOver_of_comap_eq rfl
  show psiFactor (w.comap (algebraMap E F)) w ((x.1 (w.comap (algebraMap E F))) ⊗ₜ[E] (1 : F)) = _
  rw [psiFactor_tmul, map_one, mul_one]

theorem main (𝔣 : Ideal (𝓞 E)) (u : (AdeleRing (𝓞 E) E)ˣ) (hu : IsAdjuster E 𝔣 u 1) :
    IsAdjuster F (modulusExt E F 𝔣) (Units.map (genuineBaseChange E F).β.toMonoidHom u) 1 := by
  classical
  set u' := Units.map (genuineBaseChange E F).β.toMonoidHom u with hu'def
  have hcoe : (u' : AdeleRing (𝓞 F) F) = (genuineBaseChange E F).β (u : AdeleRing (𝓞 E) E) := rfl
  obtain ⟨hcong, hsign⟩ := hu
  simp only [mul_map_one_inv] at hcong hsign
  refine ⟨fun w hw => ?_, fun τ => ?_⟩
  ·
    rw [mul_map_one_inv, hcoe]
    set v := w.under (𝓞 E) with hvdef
    have hcomp : ((genuineBaseChange E F).β (u : AdeleRing (𝓞 E) E)).2 w =
        HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, rfl⟩ : v.Extension (𝓞 F))
          (((u : AdeleRing (𝓞 E) E)).2 v) := by
      rw [genuineBaseChange_β, M4aHerbrand.Bridge.genuineβ_snd, M4aHerbrand.Bridge.finiteConorm_apply]
    set φ := HeightOneSpectrum.Extension.adicCompletionSemialgHom E F (⟨w, rfl⟩ : v.Extension (𝓞 F)) with hφ
    set x := ((u : AdeleRing (𝓞 E) E)).2 v with hx
    have hval : ∀ y, Valued.v (φ y) = Valued.v y ^ v.asIdeal.ramificationIdx' w.asIdeal := fun y =>
      HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom E F (⟨w, rfl⟩ : v.Extension (𝓞 F)) y

    have hv𝔣 : v.asIdeal ∣ 𝔣 := by
      rw [Ideal.dvd_iff_le] at hw ⊢
      exact Ideal.map_le_iff_le_comap.1 hw
    obtain ⟨h1, h2⟩ := hcong v hv𝔣
    rw [hcomp]
    refine ⟨by rw [hval, h1, one_pow], ?_⟩
    rw [show φ x - 1 = φ (x - 1) by rw [map_sub, map_one], hval]
    have hx1 : Valued.v (x - 1) ≤ 1 :=
      Valuation.map_sub_le _ (le_of_eq h1) (le_of_eq (Valuation.map_one _))
    by_cases h𝔣 : 𝔣 = ⊥
    ·
      have hirr : Irreducible (Associates.mk w.asIdeal) := Associates.irreducible_mk.2 w.irreducible
      have h0 : (Associates.mk w.asIdeal).count (Associates.mk (modulusExt E F 𝔣)).factors = 0 := by
        rw [h𝔣, show modulusExt E F (⊥ : Ideal (𝓞 E)) = ⊥ from Ideal.map_bot, show Associates.mk (⊥ : Ideal (𝓞 F)) = 0 from rfl,
          Associates.factors_zero]
        unfold Associates.count
        rw [dif_pos hirr]
        rfl
      rw [h0, Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact pow_le_one₀ zero_le' hx1
    ·
      haveI : FaithfulSMul (𝓞 E) (𝓞 F) := faithfulSMul_AB (𝓞 E) E F (𝓞 F)
      have hmapne : modulusExt E F 𝔣 ≠ ⊥ := fun h =>
        h𝔣 ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 F))).1 h)
      have hn : ((Associates.mk w.asIdeal).count (Associates.mk (modulusExt E F 𝔣)).factors : ℤ) =
          ((v.asIdeal.ramificationIdx' w.asIdeal * (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℕ) : ℤ) := by
        have h := count_coe_map_ideal (𝓞 E) E F (𝓞 F) 𝔣 h𝔣 w
        rw [FractionalIdeal.count_coe F w hmapne] at h
        exact h
      rw [hn, Nat.cast_mul, neg_mul_eq_mul_neg, show ((v.asIdeal.ramificationIdx' w.asIdeal : ℕ) : ℤ) *
          -(((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℕ) : ℤ) =
          (v.asIdeal.ramificationIdx' w.asIdeal) • -(((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℕ) : ℤ) from
          (nsmul_eq_mul _ _).symm, WithZero.exp_nsmul]
      exact pow_le_pow_left₀ zero_le' h2 _
  ·
    rw [mul_map_one_inv]
    show 0 < InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_placeOf F τ) ((u' : AdeleRing (𝓞 F) F).1 (placeOf F τ))
    rw [hcoe, genuineβ_fst_apply]
    set w := placeOf F τ with hwdef
    set v := w.comap (algebraMap E F) with hvdef
    haveI : w.1.LiesOver v.1 := liesOver_of_comap_eq rfl
    have hv : v = placeOf E (τ.comp (algebraMap E F)) := by
      rw [hvdef, hwdef, placeOf, placeOf, InfinitePlace.comap_mk]; rfl
    have hvr : v.IsReal := hv ▸ isReal_placeOf E _

    have hpos : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hvr ((u : AdeleRing (𝓞 E) E).1 v) := by
      have key : ∀ (v' : InfinitePlace E) (h : v' = placeOf E (τ.comp (algebraMap E F))) (hr : v'.IsReal),
          0 < InfinitePlace.Completion.ringEquivRealOfIsReal hr ((u : AdeleRing (𝓞 E) E).1 v') := by
        rintro _ rfl hr
        exact hsign (τ.comp (algebraMap E F))
      exact key v hv hvr

    set r := InfinitePlace.Completion.ringEquivRealOfIsReal hvr with hr
    set y := (u : AdeleRing (𝓞 E) E).1 v with hy
    let f : ℝ →+* ℝ := (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_placeOf F τ)).toRingHom.comp
      ((algebraMap v.Completion w.Completion).comp r.symm.toRingHom)
    have hf : ∀ t, f t = t := fun t => by rw [Subsingleton.elim f (RingHom.id ℝ)]; rfl
    have : InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_placeOf F τ) (algebraMap v.Completion w.Completion y) = f (r y) := by
      show _ = InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_placeOf F τ) (algebraMap v.Completion w.Completion (r.symm (r y)))
      rw [RingEquiv.symm_apply_apply]
    rw [this, hf]
    exact hpos

end main

end

end P2mS25BADJ

theorem solution
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (𝔣 : Ideal (𝓞 E)) (u : (AdeleRing (𝓞 E) E)ˣ) (hu : IsAdjuster E 𝔣 u 1) :
    IsAdjuster F (modulusExt E F 𝔣) (Units.map (genuineBaseChange E F).β.toMonoidHom u) 1 :=
  P2mS25BADJ.main E F 𝔣 u hu

end S_HeckeCharacter_isAdjuster_unitsMap_genuineBaseChange_one_of_isAdjuster_one
end P2MW
export P2MW.S_HeckeCharacter_isAdjuster_unitsMap_genuineBaseChange_one_of_isAdjuster_one (solution)
