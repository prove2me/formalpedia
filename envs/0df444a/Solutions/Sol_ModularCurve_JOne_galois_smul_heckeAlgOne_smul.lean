-- Prove2me | solution 1 for ModularCurve.JOne.galois_smul_heckeAlgOne_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4e39519f-95a1-5b87-99f8-6b1ded17573e

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JOne_galois_smul_heckeAlgOne_smul

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IntermediateField HahnSeries

namespace ModularCurve
p2m_export "ModularCurve" "HeckeAlgOne heckeOperatorOneBar_apply heckeDiamondGenBar heckeDiamondGenBar_inl heckeDiamondGenBar_inr HeckeDiamondCommuteBar heckeEvalOneBar heckeEvalOneBar_X heckeEvalOneBar_C heckeModuleOneBar heckeModuleOneBar_smul_def heckeModuleOneBar_smul_of_not heckeAlphaOneBar coe_heckeAlphaOneBar HeckeBetaOneDefined heckeBetaOneBar heckeBetaOneBar_of_not coe_heckeBetaOneBar HeckeInputsOneAlong heckeOperatorOneAlong heckeOperatorOneAlong_eq heckeOperatorOneAlong_of_not x1FunctionField x1x0FunctionFieldC x1FunctionFieldBar JOne arithmeticRingAut coe_arithmeticRingAut_apply arithmeticGalois coe_arithmeticGalois_smul galois_smul_pic0_def qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd coeffMap coeffMap_coeff coeffMap_algebraMap coeffEmb coeffMap_coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff IsBaseChangeAutOf baseChangeAut isBaseChangeAutOf_baseChangeAut baseChangeAut_of_not diamondAut diamondAutBar diamondOneBar diamondOneBar_apply"
p2m_open "ModularCurve"

namespace JOneGaloisHeckeComm

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
variable (M : ℕ) (ℓ : ℕ) [NeZero ℓ]

omit [NeZero ℓ] in

theorem intertwines_alpha (σ : L ≃ₐ[ℚ] L) :
    SemilinearAut.IntertwinesAlong (heckeAlphaOneBar L M ℓ).toRingHom
      (arithmeticGalois (x1FunctionField M) σ)
      (arithmeticGalois (x1x0FunctionFieldC ℚ M (M * ℓ)) σ) := by
  intro x
  apply Subtype.ext
  change ((arithmeticGalois (x1x0FunctionFieldC ℚ M (M * ℓ)) σ • heckeAlphaOneBar L M ℓ x :
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) : LaurentSeries L) =
    ((heckeAlphaOneBar L M ℓ (arithmeticGalois (x1FunctionField M) σ • x) :
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) : LaurentSeries L)
  rw [coe_arithmeticGalois_smul, coe_heckeAlphaOneBar, coe_heckeAlphaOneBar,
    coe_arithmeticGalois_smul]

theorem intertwines_beta (σ : L ≃ₐ[ℚ] L) :
    SemilinearAut.IntertwinesAlong (heckeBetaOneBar L M ℓ).toRingHom
      (arithmeticGalois (x1FunctionField M) σ)
      (arithmeticGalois (x1x0FunctionFieldC ℚ M (M * ℓ)) σ) := by
  rcases Classical.em (HeckeBetaOneDefined M ℓ) with h | h
  · intro x
    apply Subtype.ext
    change ((arithmeticGalois (x1x0FunctionFieldC ℚ M (M * ℓ)) σ • heckeBetaOneBar L M ℓ x :
        laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) : LaurentSeries L) =
      ((heckeBetaOneBar L M ℓ (arithmeticGalois (x1FunctionField M) σ • x) :
        laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) : LaurentSeries L)
    rw [coe_arithmeticGalois_smul, coe_heckeBetaOneBar M ℓ h, coe_heckeBetaOneBar M ℓ h,
      coe_arithmeticGalois_smul, coeffMap_qExpand_comm]
  · rw [heckeBetaOneBar_of_not M ℓ h]
    exact intertwines_alpha M ℓ σ

theorem galois_smul_heckeOperatorOneAlong (σ : L ≃ₐ[ℚ] L)
    (P : Pic0 L (laurentBaseChange L (x1FunctionField M))) :
    σ • heckeOperatorOneAlong L M ℓ P = heckeOperatorOneAlong L M ℓ (σ • P) := by
  rcases Classical.em (HeckeInputsOneAlong L M ℓ) with h | h
  · obtain ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩ := h
    rw [heckeOperatorOneAlong_eq h0 hα hβ hFI hfin hN, galois_smul_pic0_def, galois_smul_pic0_def]
    exact (SemilinearAut.pic0_correspondence_smul
      (g := arithmeticGalois (x1FunctionField M) σ)
      (g' := arithmeticGalois (x1x0FunctionFieldC ℚ M (M * ℓ)) σ)
      (heckeBetaOneBar L M ℓ) (heckeAlphaOneBar L M ℓ) hβ hα hFI hfin hN
      (intertwines_beta M ℓ σ) (intertwines_alpha M ℓ σ) P).symm
  · rw [heckeOperatorOneAlong_of_not h, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, smul_zero]

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

theorem ringHom_apply_eq_of_eqOn {X : Type*} [DivisionRing X]
    {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (f₁ f₂ : laurentBaseChange L F₀ →+* X)
    (hconst : ∀ (a : L) (ha : algebraMap L (LaurentSeries L) a ∈ laurentBaseChange L F₀),
      f₁ ⟨algebraMap L (LaurentSeries L) a, ha⟩ = f₂ ⟨algebraMap L (LaurentSeries L) a, ha⟩)
    (hgen : ∀ (y : LaurentSeries ℚ) (hy : y ∈ F₀),
      f₁ ⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L hy⟩ =
        f₂ ⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L hy⟩)
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

  have hx := x.2
  rw [mem_laurentBaseChange_iff] at hx
  refine (Subfield.closure_le.mpr ?_) hx
  rintro _ (⟨a, rfl⟩ | ⟨z, hz, rfl⟩)
  · exact hT ⟨algebraMap L (LaurentSeries L) a, (laurentBaseChange L F₀).algebraMap_mem a⟩
      (hconst a _)
  · exact hT ⟨coeffEmb L z, coeffEmb_mem_laurentBaseChange L hz⟩ (hgen z hz)

theorem arithmeticRingAut_comm_of_rational
    {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}
    (τ : laurentBaseChange L F₀ →+* laurentBaseChange L F₀)
    (hτL : ∀ (a : L) (ha : algebraMap L (LaurentSeries L) a ∈ laurentBaseChange L F₀),
      τ ⟨algebraMap L (LaurentSeries L) a, ha⟩ = ⟨algebraMap L (LaurentSeries L) a, ha⟩)
    (hτ : ∀ (y : LaurentSeries ℚ) (hy : y ∈ F₀), ∃ y' : LaurentSeries ℚ,
      ((τ ⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L hy⟩ : laurentBaseChange L F₀) :
        LaurentSeries L) = coeffEmb L y')
    (σ : L ≃ₐ[ℚ] L) (x : laurentBaseChange L F₀) :
    arithmeticRingAut F₀ σ (τ x) = τ (arithmeticRingAut F₀ σ x) := by
  refine ringHom_apply_eq_of_eqOn (X := laurentBaseChange L F₀)
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
    intro y hy
    obtain ⟨y', hy'⟩ := hτ y hy
    have hfix : arithmeticRingAut F₀ σ
        (⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L hy⟩ : laurentBaseChange L F₀) =
          ⟨coeffEmb L y, coeffEmb_mem_laurentBaseChange L hy⟩ :=
      Subtype.ext (coeffMap_coeffEmb σ y)
    change arithmeticRingAut F₀ σ (τ _) = τ (arithmeticRingAut F₀ σ _)
    rw [hfix]
    apply Subtype.ext
    rw [coe_arithmeticRingAut_apply, hy', coeffMap_coeffEmb]

end Rational

section Diamond

variable (M : ℕ)

theorem isBaseChangeAutOf_rational {d : ℕ}
    {τ : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M}
    (hτ : IsBaseChangeAutOf (AlgebraicClosure ℚ) (diamondAut M d) τ)
    (y : LaurentSeries ℚ) (hy : y ∈ x1FunctionField M) :
    ∃ y' : LaurentSeries ℚ,
      (((τ : x1FunctionFieldBar M →+* x1FunctionFieldBar M)
          ⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hy⟩ :
            x1FunctionFieldBar M) : LaurentSeries (AlgebraicClosure ℚ))
        = coeffEmb (AlgebraicClosure ℚ) y' :=
  ⟨((diamondAut M d ⟨y, hy⟩ : x1FunctionField M) : LaurentSeries ℚ), hτ ⟨y, hy⟩⟩

theorem arithmeticRingAut_diamondAutBar_comm (d : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : x1FunctionFieldBar M) :
    arithmeticRingAut (x1FunctionField M) σ
        ((diamondAutBar M d : x1FunctionFieldBar M →+* x1FunctionFieldBar M) x) =
      (diamondAutBar M d : x1FunctionFieldBar M →+* x1FunctionFieldBar M)
        (arithmeticRingAut (x1FunctionField M) σ x) := by
  rcases Classical.em
      (∃ τ : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M,
        IsBaseChangeAutOf (AlgebraicClosure ℚ) (diamondAut M d) τ) with hex | hex
  · exact arithmeticRingAut_comm_of_rational
      (diamondAutBar M d : x1FunctionFieldBar M →+* x1FunctionFieldBar M)
      (fun a _ => (diamondAutBar M d).commutes a)
      (isBaseChangeAutOf_rational M (isBaseChangeAutOf_baseChangeAut hex)) σ x
  · have hrefl : diamondAutBar M d = AlgEquiv.refl := baseChangeAut_of_not hex
    rw [hrefl]
    rfl

theorem arithmeticGalois_mul_ofAlgAut_diamondAutBar (d : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (x1FunctionField M) σ * SemilinearAut.ofAlgAut (diamondAutBar M d) =
      SemilinearAut.ofAlgAut (diamondAutBar M d) * arithmeticGalois (x1FunctionField M) σ :=
  mul_ofAlgAut_comm _ _ (arithmeticRingAut_diamondAutBar_comm M d σ)

theorem galois_smul_diamondOneBar (d : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P : JOne M) :
    σ • diamondOneBar M d P = diamondOneBar M d (σ • P) := by
  rw [diamondOneBar_apply, diamondOneBar_apply, galois_smul_pic0_def, galois_smul_pic0_def]
  exact smul_smul_comm_of_mul_comm _ _ (arithmeticGalois_mul_ofAlgAut_diamondAutBar M d σ) P

end Diamond

section Assembly

variable (M : ℕ)

theorem galois_smul_heckeDiamondGenBar (i : Nat.Primes ⊕ ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JOne M) :
    σ • heckeDiamondGenBar M i x = heckeDiamondGenBar M i (σ • x) := by
  cases i with
  | inl ℓ =>
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
      rw [heckeDiamondGenBar_inl, heckeOperatorOneBar_apply, heckeOperatorOneBar_apply]
      exact galois_smul_heckeOperatorOneAlong M ℓ σ x
  | inr d =>
      rw [heckeDiamondGenBar_inr]
      exact galois_smul_diamondOneBar M d σ x

theorem galois_smul_heckeEvalOneBar (h : HeckeDiamondCommuteBar M)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : HeckeAlgOne) :
    ∀ x : JOne M, σ • heckeEvalOneBar h t x = heckeEvalOneBar h t (σ • x) := by
  refine MvPolynomial.induction_on
    (motive := fun t => ∀ x : JOne M, σ • heckeEvalOneBar h t x = heckeEvalOneBar h t (σ • x))
    t ?_ ?_ ?_
  · intro a x
    rw [heckeEvalOneBar_C, Module.End.intCast_apply, Module.End.intCast_apply, galois_smul_pic0_def,
      galois_smul_pic0_def]
    exact SemilinearAut.smul_zsmul _ a x
  · intro p q hp hq x
    rw [RingHom.map_add, LinearMap.add_apply, LinearMap.add_apply, smul_add, hp, hq]
  · intro p i hp x
    rw [RingHom.map_mul, Module.End.mul_apply, Module.End.mul_apply, heckeEvalOneBar_X, hp,
      galois_smul_heckeDiamondGenBar]

theorem galois_smul_hecke_smul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : HeckeAlgOne)
    (x : JOne M) :
    (letI := heckeModuleOneBar M; σ • (t • x)) = (letI := heckeModuleOneBar M; t • (σ • x)) := by
  by_cases h : HeckeDiamondCommuteBar M
  · rw [heckeModuleOneBar_smul_def h, heckeModuleOneBar_smul_def h]
    exact galois_smul_heckeEvalOneBar M h σ t x
  · rw [heckeModuleOneBar_smul_of_not h, heckeModuleOneBar_smul_of_not h, galois_smul_pic0_def,
      galois_smul_pic0_def]
    exact SemilinearAut.smul_zsmul _ _ x

end Assembly

end JOneGaloisHeckeComm

end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_JOne_galois_smul_heckeAlgOne_smul.ModularCurve ModularCurve.JOneGaloisHeckeComm in

theorem solution (M : ℕ) [NeZero M]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : ModularCurve.HeckeAlgOne)
    (x : ModularCurve.JOne M) :
    letI := ModularCurve.heckeModuleOneBar M
    σ • (t • x) = t • (σ • x) :=
  galois_smul_hecke_smul M σ t x

end S_ModularCurve_JOne_galois_smul_heckeAlgOne_smul
end P2MW
export P2MW.S_ModularCurve_JOne_galois_smul_heckeAlgOne_smul (solution)
