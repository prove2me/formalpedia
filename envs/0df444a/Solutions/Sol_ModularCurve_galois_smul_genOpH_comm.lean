-- Prove2me | solution 1 for ModularCurve.galois_smul_genOpH_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/94275c09-306e-5a62-9556-ae9d70d0ddaf

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_galois_smul_genOpH_comm

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IntermediateField HahnSeries

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "IsDiamondAutHBar diamondAutHBar isDiamondAutHBar_diamondAutHBar diamondHBar diamondHBar_apply diamondHBar_of_not genOpH heckeAlphaHBar coe_heckeAlphaHBar HeckeBetaHDefined heckeBetaHBar heckeBetaHBar_of_not coe_heckeBetaHBar HeckeInputsHAlong heckeOperatorHAlong heckeOperatorHAlong_eq heckeOperatorHAlong_of_not xHFunctionField xHTopFunctionFieldC xHFunctionFieldBar JH intFormRatiosC intFormRatiosC_subset arithmeticRingAut coe_arithmeticRingAut_apply arithmeticGalois coe_arithmeticGalois_smul galois_smul_pic0_def qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd coeffMap coeffMap_coeff coeffMap_algebraMap coeffEmb coeffMap_coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff"
p2m_open "ModularCurve"

namespace GaloisSmulGenOpHComm

theorem coeffMap_qExpand_comm {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

section Hecke

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

omit [NeZero ℓ] in

theorem intertwines_alpha (σ : L ≃ₐ[ℚ] L) :
    SemilinearAut.IntertwinesAlong (heckeAlphaHBar L M H ℓ).toRingHom
      (arithmeticGalois (xHFunctionField M H) σ)
      (arithmeticGalois (xHTopFunctionFieldC ℚ M H (M * ℓ)) σ) := by
  intro x
  apply Subtype.ext
  change ((arithmeticGalois (xHTopFunctionFieldC ℚ M H (M * ℓ)) σ • heckeAlphaHBar L M H ℓ x :
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries L) =
    ((heckeAlphaHBar L M H ℓ (arithmeticGalois (xHFunctionField M H) σ • x) :
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries L)
  rw [coe_arithmeticGalois_smul, coe_heckeAlphaHBar, coe_heckeAlphaHBar, coe_arithmeticGalois_smul]

theorem intertwines_beta (σ : L ≃ₐ[ℚ] L) :
    SemilinearAut.IntertwinesAlong (heckeBetaHBar L M H ℓ).toRingHom
      (arithmeticGalois (xHFunctionField M H) σ)
      (arithmeticGalois (xHTopFunctionFieldC ℚ M H (M * ℓ)) σ) := by
  rcases Classical.em (HeckeBetaHDefined M H ℓ) with h | h
  · intro x
    apply Subtype.ext
    change ((arithmeticGalois (xHTopFunctionFieldC ℚ M H (M * ℓ)) σ • heckeBetaHBar L M H ℓ x :
        laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries L) =
      ((heckeBetaHBar L M H ℓ (arithmeticGalois (xHFunctionField M H) σ • x) :
        laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries L)
    rw [coe_arithmeticGalois_smul, coe_heckeBetaHBar M H ℓ h, coe_heckeBetaHBar M H ℓ h,
      coe_arithmeticGalois_smul, coeffMap_qExpand_comm]
  · rw [heckeBetaHBar_of_not M H ℓ h]
    exact intertwines_alpha M H ℓ σ

theorem galois_smul_heckeOperatorHAlong (σ : L ≃ₐ[ℚ] L)
    (P : Pic0 L (laurentBaseChange L (xHFunctionField M H))) :
    σ • heckeOperatorHAlong L M H ℓ P = heckeOperatorHAlong L M H ℓ (σ • P) := by
  rcases Classical.em (HeckeInputsHAlong L M H ℓ) with h | h
  · obtain ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩ := h
    rw [heckeOperatorHAlong_eq h0 hα hβ hFI hfin hN, galois_smul_pic0_def, galois_smul_pic0_def]
    exact (SemilinearAut.pic0_correspondence_smul
      (g := arithmeticGalois (xHFunctionField M H) σ)
      (g' := arithmeticGalois (xHTopFunctionFieldC ℚ M H (M * ℓ)) σ)
      (heckeBetaHBar L M H ℓ) (heckeAlphaHBar L M H ℓ) hβ hα hFI hfin hN
      (intertwines_beta M H ℓ σ) (intertwines_alpha M H ℓ σ) P).symm
  · rw [heckeOperatorHAlong_of_not h, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, smul_zero]

end Hecke

section Semilinear

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mul_ofAlgAut_comm (g : SemilinearAut K F) (τ : F ≃ₐ[K] F)
    (h : ∀ x : F, g • (τ x) = τ (g • x)) :
    g * SemilinearAut.ofAlgAut τ = SemilinearAut.ofAlgAut τ * g := by
  apply Subtype.ext
  apply Prod.ext
  · apply RingEquiv.ext
    intro x
    exact h x
  · apply RingEquiv.ext
    intro a
    change (SemilinearAut.baseAut g * 1) a = (1 * SemilinearAut.baseAut g) a
    rw [mul_one, one_mul]

theorem smul_smul_comm_of_mul_comm (A B : SemilinearAut K F) (h : A * B = B * A) (P : Pic0 K F) :
    A • (B • P) = B • (A • P) := by
  rw [← mul_smul, ← mul_smul, h]

end Semilinear

section Rational

variable {L : Type*} [Field L] [Algebra ℚ L]

theorem ringHom_apply_eq_of_eqOn_generators {X : Type*} [DivisionRing X]
    {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} {R : Set (LaurentSeries ℚ)} (hRF : R ⊆ F₀)
    (hFR : F₀ ≤ IntermediateField.adjoin ℚ R) (f₁ f₂ : laurentBaseChange L F₀ →+* X)
    (hconst : ∀ (a : L) (ha : algebraMap L (LaurentSeries L) a ∈ laurentBaseChange L F₀),
      f₁ ⟨algebraMap L (LaurentSeries L) a, ha⟩ = f₂ ⟨algebraMap L (LaurentSeries L) a, ha⟩)
    (hgen : ∀ (r : LaurentSeries ℚ) (hr : r ∈ R),
      f₁ ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩ =
        f₂ ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩)
    (x : laurentBaseChange L F₀) : f₁ x = f₂ x := by

  let T : Subfield (LaurentSeries L) :=
    (RingHom.eqLocusField f₁ f₂).map (SubringClass.subtype (laurentBaseChange L F₀))
  have hT : ∀ z : laurentBaseChange L F₀, f₁ z = f₂ z → (z : LaurentSeries L) ∈ T := fun z hz =>
    Subfield.mem_map.mpr ⟨z, hz, rfl⟩

  suffices hx : (x : LaurentSeries L) ∈ T by
    obtain ⟨x', hx', hx'x⟩ := Subfield.mem_map.mp hx
    have hxx : x' = x := Subtype.ext hx'x
    subst hxx
    exact hx'

  have hgenT : ∀ r ∈ R, coeffEmb L r ∈ T := fun r hr =>
    hT ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩ (hgen r hr)

  have hF₀ : ∀ z ∈ F₀, coeffEmb L z ∈ T := by
    intro z hz
    have hz' : z ∈ (IntermediateField.adjoin ℚ R).toSubfield :=
      (IntermediateField.mem_toSubfield _ _).mpr (hFR hz)
    rw [IntermediateField.adjoin_toSubfield] at hz'
    have hle : Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ R) ≤
        T.comap (coeffEmb L) := by
      rw [Subfield.closure_le]
      rintro w (⟨a, rfl⟩ | hw)
      · rw [SetLike.mem_coe, Subfield.mem_comap, eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) a,
          map_ratCast]
        exact SubfieldClass.ratCast_mem T a
      · rw [SetLike.mem_coe, Subfield.mem_comap]
        exact hgenT w hw
    exact Subfield.mem_comap.mp (hle hz')

  have hx := x.2
  rw [mem_laurentBaseChange_iff] at hx
  refine (Subfield.closure_le.mpr ?_) hx
  rintro _ (⟨a, rfl⟩ | ⟨z, hz, rfl⟩)
  · exact hT ⟨algebraMap L (LaurentSeries L) a, (laurentBaseChange L F₀).algebraMap_mem a⟩
      (hconst a _)
  · exact hF₀ z hz

theorem arithmeticRingAut_comm_of_rational_on_generators
    {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} {R : Set (LaurentSeries ℚ)} (hRF : R ⊆ F₀)
    (hFR : F₀ ≤ IntermediateField.adjoin ℚ R)
    (τ : laurentBaseChange L F₀ →+* laurentBaseChange L F₀)
    (hτL : ∀ (a : L) (ha : algebraMap L (LaurentSeries L) a ∈ laurentBaseChange L F₀),
      τ ⟨algebraMap L (LaurentSeries L) a, ha⟩ = ⟨algebraMap L (LaurentSeries L) a, ha⟩)
    (hτ : ∀ (r : LaurentSeries ℚ) (hr : r ∈ R), ∃ y : LaurentSeries ℚ,
      ((τ ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩ : laurentBaseChange L F₀) :
        LaurentSeries L) = coeffEmb L y)
    (σ : L ≃ₐ[ℚ] L) (x : laurentBaseChange L F₀) :
    arithmeticRingAut F₀ σ (τ x) = τ (arithmeticRingAut F₀ σ x) := by
  refine ringHom_apply_eq_of_eqOn_generators (X := laurentBaseChange L F₀) hRF hFR
    ((arithmeticRingAut F₀ σ).toRingHom.comp τ) (τ.comp (arithmeticRingAut F₀ σ).toRingHom)
    ?_ ?_ x
  ·
    intro a ha
    have h1 : ∀ (b : L) (hb : algebraMap L (LaurentSeries L) b ∈ laurentBaseChange L F₀),
        arithmeticRingAut F₀ σ ⟨algebraMap L (LaurentSeries L) b, hb⟩ =
          ⟨algebraMap L (LaurentSeries L) (σ b), (laurentBaseChange L F₀).algebraMap_mem (σ b)⟩ :=
      fun b hb => Subtype.ext (coeffMap_algebraMap (σ : L →+* L) b)
    change arithmeticRingAut F₀ σ (τ _) = τ (arithmeticRingAut F₀ σ _)
    rw [hτL a ha, h1, hτL]
  ·
    intro r hr
    obtain ⟨y, hy⟩ := hτ r hr
    have hfix : arithmeticRingAut F₀ σ
        (⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩ : laurentBaseChange L F₀) =
          ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩ :=
      Subtype.ext (coeffMap_coeffEmb σ r)
    change arithmeticRingAut F₀ σ (τ _) = τ (arithmeticRingAut F₀ σ _)
    rw [hfix]
    apply Subtype.ext
    rw [coe_arithmeticRingAut_apply, hy, coeffMap_coeffEmb]

end Rational

section Diamond

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem isDiamondAutHBar_rational {d : (ZMod M)ˣ}
    {τ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H}
    (hτ : IsDiamondAutHBar M H d τ) (r : LaurentSeries ℚ)
    (hr : r ∈ intFormRatiosC ℚ (CohCarrier.GammaH M H)) :
    ∃ y : LaurentSeries ℚ,
      (((τ : xHFunctionFieldBar M H →+* xHFunctionFieldBar M H)
          ⟨coeffEmb (AlgebraicClosure ℚ) r, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (intFormRatiosC_subset ℚ (CohCarrier.GammaH M H) hr)⟩ : xHFunctionFieldBar M H) :
        LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) y := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hr

  obtain ⟨γ, hγ⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  have h00 : (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
    have h1 : (((CohCarrier.gamma0Units M γ)⁻¹ : (ZMod M)ˣ) : ZMod M) =
        (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) := rfl
    rw [← h1, hγ, inv_inv]
  obtain ⟨y, -, hy, -⟩ := hτ k f g pf pg hf hg hg0 γ γ.2 h00
  exact ⟨y, hy⟩

theorem arithmeticRingAut_diamondAutHBar_comm {d : (ZMod M)ˣ}
    (hτ : IsDiamondAutHBar M H d (diamondAutHBar M H d))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : xHFunctionFieldBar M H) :
    arithmeticRingAut (xHFunctionField M H) σ
        ((diamondAutHBar M H d : xHFunctionFieldBar M H →+* xHFunctionFieldBar M H) x) =
      (diamondAutHBar M H d : xHFunctionFieldBar M H →+* xHFunctionFieldBar M H)
        (arithmeticRingAut (xHFunctionField M H) σ x) :=
  arithmeticRingAut_comm_of_rational_on_generators
    (intFormRatiosC_subset ℚ (CohCarrier.GammaH M H)) le_rfl
    (diamondAutHBar M H d : xHFunctionFieldBar M H →+* xHFunctionFieldBar M H)
    (fun a _ => (diamondAutHBar M H d).commutes a)
    (isDiamondAutHBar_rational M H hτ) σ x

theorem arithmeticGalois_mul_ofAlgAut_diamondAutHBar {d : (ZMod M)ˣ}
    (hτ : IsDiamondAutHBar M H d (diamondAutHBar M H d))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (xHFunctionField M H) σ * SemilinearAut.ofAlgAut (diamondAutHBar M H d) =
      SemilinearAut.ofAlgAut (diamondAutHBar M H d) * arithmeticGalois (xHFunctionField M H) σ :=
  mul_ofAlgAut_comm _ _ (arithmeticRingAut_diamondAutHBar_comm M H hτ σ)

theorem galois_smul_diamondHBar (d : (ZMod M)ˣ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P : JH M H) :
    σ • diamondHBar M H d P = diamondHBar M H d (σ • P) := by
  rcases Classical.em (∃ τ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d τ) with hex | hex
  · rw [diamondHBar_apply, diamondHBar_apply, galois_smul_pic0_def, galois_smul_pic0_def]
    exact smul_smul_comm_of_mul_comm _ _
      (arithmeticGalois_mul_ofAlgAut_diamondAutHBar M H (isDiamondAutHBar_diamondAutHBar hex) σ) P
  · rw [diamondHBar_of_not M H hex, diamondHBar_of_not M H hex]

end Diamond

end GaloisSmulGenOpHComm

end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_galois_smul_genOpH_comm.ModularCurve ModularCurve.GaloisSmulGenOpHComm in

theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (g : CohCarrier.Gen M S)
    (P : ModularCurve.JH M H) :
    σ • (ModularCurve.genOpH M H S g P) = ModularCurve.genOpH M H S g (σ • P) := by
  cases g with
  | T ℓ hℓ hℓS hℓM =>
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      exact galois_smul_heckeOperatorHAlong M H ℓ σ P
  | U q hq hqM =>
      haveI : NeZero q := ⟨hq.ne_zero⟩
      exact galois_smul_heckeOperatorHAlong M H q σ P
  | dia d => exact galois_smul_diamondHBar M H d σ P

end S_ModularCurve_galois_smul_genOpH_comm
end P2MW
export P2MW.S_ModularCurve_galois_smul_genOpH_comm (solution)
