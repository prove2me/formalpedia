-- Prove2me | solution 1 for N25.five_qPlaces_distinct
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:47.461363+00:00
-- url     : https://prove2.me/submissions/d1c49626-27fa-43c6-aac8-e99e153a3e18

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_N25_qPlace_witnesses
import Theorems.Thm_N25_qPlace_rigidity
import Theorems.Thm_N25_qPlace_galois_fixed
import Theorems.Thm_N25_diamondField_fixes_jq
import Theorems.Thm_N25_diamondField_galois_comm
import Theorems.Thm_N25_diamondField_order_five
import Theorems.Thm_N25_exists_forget_algEquiv_action
import Theorems.Thm_ModularCurve_order_coeffMap
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_deg_qInftyPlaceRat
import Theorems.Thm_ModularCurve_diamondAutHBar_mul_and_diamondAutHBar_one
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace N25

private theorem power_fixes {K F : Type*} [Field K] [Field F] [Algebra K F]
    (τ : F ≃ₐ[K] F) (x : F) (h : τ x = x) (n : ℕ) : (τ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ]
    change (τ ^ n) (τ x) = x
    rw [h, ih]

private theorem orbit_injective
    (K : Type*) [Field K] (F : IntermediateField K (LaurentSeries K))
    (h : ∃ j : F, (qSeriesBar K F j).order = -1)
    (τ : F ≃ₐ[K] F) (j : F) (hj : (qSeriesBar K F j).order = -1)
    (hτj : τ j = j) (horder : orderOf τ = 5) :
    Function.Injective (fun i : Fin 5 =>
      (SemilinearAut.ofAlgAut τ)^i.val • qInftyPlaceBar K F h) := by
  intro i k hik
  change (SemilinearAut.ofAlgAut τ)^i.val • qInftyPlaceBar K F h =
    (SemilinearAut.ofAlgAut τ)^k.val • qInftyPlaceBar K F h at hik
  have hf : SemilinearAut.ofAlgAut ((τ^i.val)⁻¹ * τ^k.val) •
      qInftyPlaceBar K F h = qInftyPlaceBar K F h := by
    rw [map_mul, map_inv, map_pow, map_pow, mul_smul, ← hik, inv_smul_smul]
  have hjinv : ((τ^i.val)⁻¹) j = j := by
    apply (τ^i.val).injective
    change (τ^i.val) (((τ^i.val).symm) j) = (τ^i.val) j
    rw [AlgEquiv.apply_symm_apply, power_fixes τ j hτj]
  have he := qPlace_rigidity K F h ((τ^i.val)⁻¹ * τ^k.val) j hj
    (by change ((τ^i.val)⁻¹) ((τ^k.val) j) = j
        rw [power_fixes τ j hτj, hjinv]) hf
  have hp : τ^i.val = τ^k.val := inv_mul_eq_one.mp he
  apply Fin.ext
  exact pow_injOn_Iio_orderOf
    (by simpa only [Set.mem_Iio, horder] using i.isLt)
    (by simpa only [Set.mem_Iio, horder] using k.isLt) hp

private theorem rational_orbit_injective
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (h₀ : ∃ j : F₀, (qSeriesBar ℚ F₀ j).order = -1)
    (τ₀ : F₀ ≃ₐ[ℚ] F₀) (j₀ : F₀)
    (ho₀ : (qSeriesBar ℚ F₀ j₀).order = -1) (hτj : τ₀ j₀ = j₀)
    (hτorder : orderOf τ₀ = 5) :
    Function.Injective (fun i : Fin 5 =>
      (SemilinearAut.ofAlgAut τ₀)^i.val • qInftyPlaceRat F₀ h₀) := by
  let τb := @RingEquiv.toRatAlgEquiv F₀ F₀ _ _
    (SubalgebraClass.toAlgebra F₀) (SubalgebraClass.toAlgebra F₀) τ₀.toRingEquiv
  have hbpow : τb^5 = 1 := by
    refine DFunLike.ext _ _ ?_
    intro x
    have e := congrArg (fun t : F₀ ≃ₐ[ℚ] F₀ => t x)
      (orderOf_dvd_iff_pow_eq_one.mp (show orderOf τ₀ ∣ 5 by rw [hτorder]))
    exact e
  have hbne : τb ≠ 1 := by
    intro he
    have ht : τ₀ = 1 := by
      apply AlgEquiv.ext
      intro x
      exact congrArg (fun t => t x) he
    have ho' := orderOf_eq_one_iff.mpr ht
    omega
  have hbo : orderOf τb = 5 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp
      (orderOf_dvd_of_pow_eq_one hbpow) with he | he
    · exact False.elim (hbne (orderOf_eq_one_iff.mp he))
    · exact he
  have hinj := orbit_injective ℚ F₀ h₀ τb j₀ ho₀ hτj hbo
  intro i k hik
  apply hinj
  apply @Place.toValuationSubring_injective ℚ F₀ _ _ (SubalgebraClass.toAlgebra F₀)
  exact congrArg (fun v : Place ℚ F₀ => v.toValuationSubring) hik

private theorem galois_orbit_fixed
    (d : (ZMod 25)ˣ)
    (h : ∃ j : xHFunctionFieldBar 25 H25,
      (qSeriesBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) j).order = -1)
    (σ : Gal) (n : ℕ) :
    arithmeticGalois (xHFunctionField 25 H25) σ •
      (SemilinearAut.ofAlgAut (diamondAutHBar 25 H25 d))^n •
        qInftyPlaceBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) h =
      (SemilinearAut.ofAlgAut (diamondAutHBar 25 H25 d))^n •
        qInftyPlaceBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) h := by
  let F₀ := xHFunctionField 25 H25
  let γ := diamondAutHBar 25 H25 d
  have hcomm : arithmeticGalois F₀ σ * SemilinearAut.ofAlgAut γ =
      SemilinearAut.ofAlgAut γ * arithmeticGalois F₀ σ := by
    apply Subtype.ext
    apply Prod.ext
    · apply RingEquiv.ext
      intro x
      exact diamondField_galois_comm d σ x
    · rfl
  have hc : Commute (arithmeticGalois F₀ σ) (SemilinearAut.ofAlgAut γ) := hcomm
  have hpowcomm := hc.pow_right n
  rw [← mul_smul, hpowcomm.eq, mul_smul, qPlace_galois_fixed h σ]

private theorem orbit_order_comparison
    (h₀ : ∃ j : xHFunctionField 25 H25,
      (qSeriesBar ℚ (xHFunctionField 25 H25) j).order = -1)
    (h : ∃ j : xHFunctionFieldBar 25 H25,
      (qSeriesBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) j).order = -1)
    (τ₀ : xHFunctionField 25 H25 ≃ₐ[ℚ] xHFunctionField 25 H25)
    (γ : xHFunctionFieldBar 25 H25 ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar 25 H25)
    (hpinpow : ∀ n : ℕ, ∀ x : xHFunctionField 25 H25,
      (γ^n) ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ =
      ⟨coeffEmb (AlgebraicClosure ℚ) ((τ₀^n) x : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) ((τ₀^n) x).2⟩)
    (n : ℕ) (x : xHFunctionField 25 H25) :
    ((SemilinearAut.ofAlgAut γ)^n •
      qInftyPlaceBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) h).ord
      ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ =
    ((SemilinearAut.ofAlgAut τ₀)^n • qInftyPlaceRat (xHFunctionField 25 H25) h₀).ord x := by
  let K := AlgebraicClosure ℚ
  let F₀ := xHFunctionField 25 H25
  let F := xHFunctionFieldBar 25 H25
  let ι : F₀ → F := fun y =>
    ⟨coeffEmb K (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange K y.2⟩
  have hpinv : (γ^n)⁻¹ (ι x) = ι ((τ₀^n)⁻¹ x) := by
    apply (γ^n).injective
    change (γ^n) ((γ^n).symm (ι x)) =
      (γ^n) (ι ((τ₀^n).symm x))
    rw [AlgEquiv.apply_symm_apply, hpinpow, AlgEquiv.apply_symm_apply]
  have hbar := SemilinearAut.ord_smul (SemilinearAut.ofAlgAut γ^n)
    (qInftyPlaceBar K F h) ((SemilinearAut.ofAlgAut γ^n)⁻¹ • ι x)
  have hrat := SemilinearAut.ord_smul (SemilinearAut.ofAlgAut τ₀^n)
    (qInftyPlaceRat F₀ h₀) ((SemilinearAut.ofAlgAut τ₀^n)⁻¹ • x)
  rw [smul_inv_smul] at hbar hrat
  rw [hbar, hrat]
  rw [← map_pow, ← map_inv, SemilinearAut.ofAlgAut_smul, hpinv]
  rw [← map_pow, ← map_inv, SemilinearAut.ofAlgAut_smul]
  have hp (y : F₀) : (qInftyPlaceRat F₀ h₀).ord y =
      (qSeriesBar ℚ F₀ y).order := by
    exact ord_qInftyPlaceBar ℚ h₀ y
  rw [hp, ord_qInftyPlaceBar]
  exact order_coeffMap (algebraMap ℚ K).injective _

/-- The five rational q-places and their geometric coefficient extensions
form the same free orbit of the label-thirteen diamond. -/
theorem _root_.solution :
    let K := AlgebraicClosure ℚ
    let F₀ := xHFunctionField 25 H25
    let F := xHFunctionFieldBar 25 H25
    let gammaF := diamondAutHBar 25 H25 (ZMod.unitOfCoprime 13 (by decide))
    ∃ h₀ : (∃ j : F₀, (qSeriesBar ℚ F₀ j).order = -1),
    ∃ h : (∃ j : F, (qSeriesBar K F j).order = -1),
    ∃ τ₀ : F₀ ≃ₐ[ℚ] F₀,
      let ι : F₀ → F := fun x =>
        ⟨coeffEmb K (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange K x.2⟩
      let p₀ : Fin 5 → Place ℚ F₀ := fun i =>
        (SemilinearAut.ofAlgAut τ₀)^i.val • qInftyPlaceRat F₀ h₀
      let p : Fin 5 → Place K F := fun i =>
        (SemilinearAut.ofAlgAut gammaF)^i.val • qInftyPlaceBar K F h
      (∀ x : F₀, gammaF (ι x) = ι (τ₀ x)) ∧
      Function.Injective p₀ ∧ Function.Injective p ∧
      (∀ i : Fin 5, (p₀ i).deg = 1 ∧ (p i).deg = 1) ∧
      (∀ σ : Gal, ∀ i : Fin 5, arithmeticGalois F₀ σ • p i = p i) ∧
      (∀ i : Fin 5, ∀ x : F₀, (p i).ord (ι x) = (p₀ i).ord x) := by
  classical
  let K := AlgebraicClosure ℚ
  let F₀ := xHFunctionField 25 H25
  let F := xHFunctionFieldBar 25 H25
  let d : (ZMod 25)ˣ := ZMod.unitOfCoprime 13 (by decide)
  let γ := diamondAutHBar 25 H25 d
  let ι : F₀ → F := fun x =>
    ⟨coeffEmb K (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange K x.2⟩
  have hi : Function.Injective ι := by
    intro x y h
    apply Subtype.ext
    apply (coeffEmb K).injective
    exact congrArg (fun z : F => (z : LaurentSeries K)) h
  obtain ⟨j₀, j, hj₀, hj, hji, ho₀, ho⟩ := qPlace_witnesses
  have hje : j = ι j₀ := Subtype.ext hji
  let h₀ : ∃ j : F₀, (qSeriesBar ℚ F₀ j).order = -1 := ⟨j₀, ho₀⟩
  let h : ∃ j : F, (qSeriesBar K F j).order = -1 := ⟨j, ho⟩
  obtain ⟨A, hA⟩ := CohCarrier.gamma0Units_surjective 25 d⁻¹
  have hA00 : (((A : SL(2,ℤ)) 0 0 : ℤ) : ZMod 25) = (d : ZMod 25) := by
    have e : (((CohCarrier.gamma0Units 25 A)⁻¹ : (ZMod 25)ˣ) : ZMod 25) =
        (((A : SL(2,ℤ)) 0 0 : ℤ) : ZMod 25) := rfl
    rw [← e, hA, inv_inv]
  obtain ⟨ρa, hρH, _, _, hρslash⟩ :=
    exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero ℚ 25 H25
  obtain ⟨ρ, hρeval⟩ := exists_forget_algEquiv_action
    (algebra := SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (CohCarrier.GammaH 25 H25))) ρa
  have hρH' : ∀ B : Gamma0 25, (B : SL(2,ℤ)) ∈ CohCarrier.GammaH 25 H25 →
      ρ B = 1 := by
    intro B hB
    ext x
    rw [hρeval, hρH B hB]
    rfl
  let τ₀ : F₀ ≃ₐ[ℚ] F₀ := (ρ A).toRatAlgEquiv
  have hpin : ∀ x : F₀, γ (ι x) = ι (τ₀ x) := by
    intro x
    apply Subtype.ext
    exact diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
      25 H25 ρ hρH' (by
        intro B k f g f₁ g₁ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ hff hgg hg0 hg₁0
        have e := congrArg (fun y : F₀ => (y : LaurentSeries ℚ))
          (hρeval B ⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
            div_mem_qExpFunctionFieldC f g hf hg hg0⟩)
        exact e.trans (hρslash B f g f₁ g₁ c hc hf hg hf₁ hg₁ hff hgg hg0 hg₁0))
      d A hA00 x
  have hpinpow : ∀ n : ℕ, ∀ x : F₀, (γ^n) (ι x) = ι ((τ₀^n) x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ]
      change (γ^n) (γ (ι x)) = ι ((τ₀^n) (τ₀ x))
      rw [hpin, ih]
  have hγj : γ j = j := by
    rw [hje]
    exact diamondField_fixes_jq d j₀ hj₀
  have hτj : τ₀ j₀ = j₀ := by
    apply hi
    rw [← hpin, ← hje, hγj]
  have hγorder : orderOf γ = 5 := by
    obtain ⟨hmul, hone⟩ := diamondAutHBar_mul_and_diamondAutHBar_one 25 H25
    let D : (ZMod 25)ˣ →* (F ≃ₐ[K] F) :=
      { toFun := diamondAutHBar 25 H25, map_one' := hone, map_mul' := hmul }
    have hd : d = (ZMod.unitOfCoprime 2 (by decide))⁻¹ := by
      apply eq_inv_iff_mul_eq_one.mpr
      apply Units.ext
      change (13 : ZMod 25) * 2 = 1
      decide
    change orderOf (D d) = 5
    rw [hd, map_inv, orderOf_inv]
    exact diamondField_order_five
  have hτorder : orderOf τ₀ = 5 := by
    have hp : τ₀^5 = 1 := by
      apply AlgEquiv.ext
      intro x
      apply hi
      have hγpow : γ^5 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hγorder])
      rw [← hpinpow, hγpow]
      rfl
    have hn : τ₀ ≠ 1 := by
      intro he
      have hjfix : γ j = j := hγj
      have hg : γ = 1 := by
        -- Equality on rational generators and constants determines the base change.
        apply AlgEquiv.ext
        intro x
        have hp : ∀ y : F₀, γ (ι y) = ι y := by
          intro y
          rw [hpin, he]
          rfl
        let γr : RingAut F := γ.toRingEquiv
        have hc : ∀ (y : LaurentSeries K) (hy : y ∈ F), γr ⟨y,hy⟩ = ⟨y,hy⟩ := by
          intro y hy
          induction hy using IntermediateField.adjoin_induction with
          | mem y hy =>
            obtain ⟨z,hz,rfl⟩ := hy
            exact hp ⟨z,hz⟩
          | algebraMap c => exact γ.commutes c
          | add y z hy hz ihy ihz =>
            change γr ((⟨y,hy⟩ : F) + ⟨z,hz⟩) = (⟨y,hy⟩ : F) + ⟨z,hz⟩
            rw [map_add, ihy, ihz]
          | mul y z hy hz ihy ihz =>
            change γr ((⟨y,hy⟩ : F) * ⟨z,hz⟩) = (⟨y,hy⟩ : F) * ⟨z,hz⟩
            rw [map_mul, ihy, ihz]
          | inv y hy ihy =>
            change γr ((⟨y,hy⟩ : F)⁻¹) = (⟨y,hy⟩ : F)⁻¹
            rw [map_inv₀, ihy]
        exact hc x.1 x.2
      have : orderOf γ = 1 := orderOf_eq_one_iff.mpr hg
      omega
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp
      (orderOf_dvd_of_pow_eq_one hp) with he | he
    · exact False.elim (hn (orderOf_eq_one_iff.mp he))
    · exact he
  refine ⟨h₀, h, τ₀, hpin, ?_, orbit_injective K F h γ j ho hγj hγorder, ?_, ?_, ?_⟩
  · exact rational_orbit_injective F₀ h₀ τ₀ j₀ ho₀ hτj hτorder

  · intro i
    exact ⟨(SemilinearAut.deg_smul _ _).trans (deg_qInftyPlaceRat h₀),
      (SemilinearAut.deg_smul _ _).trans (deg_qInftyPlaceBar K h)⟩
  · intro σ i
    exact galois_orbit_fixed d h σ i.val
  · intro i x
    exact orbit_order_comparison h₀ h τ₀ γ hpinpow i.val x

end N25
