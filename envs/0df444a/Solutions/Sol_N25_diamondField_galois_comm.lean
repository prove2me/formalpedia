-- Prove2me | solution 1 for N25.diamondField_galois_comm
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:08.216981+00:00
-- url     : https://prove2.me/submissions/0bb4abd9-fef7-43b4-be7f-a42559332a50

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_N25_exists_forget_algEquiv_action
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace N25

private theorem commutes_from_rational_generators
    {K : Type*} [Field K] [Algebra ℚ K]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (τ : laurentBaseChange K F₀ ≃ₐ[K] laurentBaseChange K F₀)
    (τ₀ : RingAut F₀)
    (hpin : ∀ x : F₀,
      τ ⟨coeffEmb K (x : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange K x.2⟩ =
        ⟨coeffEmb K ((τ₀ x : F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange K (τ₀ x).2⟩)
    (σ : K ≃ₐ[ℚ] K) (x : laurentBaseChange K F₀) :
    arithmeticGalois F₀ σ • τ x = τ (arithmeticGalois F₀ σ • x) := by
  let E := laurentBaseChange K F₀
  let t : RingAut E := τ.toRingEquiv
  let g : RingAut E := arithmeticRingAut F₀ σ
  have fixed_generator (y : F₀) :
      g ⟨coeffEmb K (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange K y.2⟩ =
        (⟨coeffEmb K (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange K y.2⟩ : E) := by
    apply Subtype.ext
    change coeffMap (σ : K →+* K) (coeffEmb K (y : LaurentSeries ℚ)) =
      coeffEmb K (y : LaurentSeries ℚ)
    exact coeffMap_coeffEmb σ _
  have ga (c : K) : g (algebraMap K E c) = algebraMap K E (σ c) := by
    exact arithmeticRingAut_algebraMap F₀ σ c
  change g (t x) = t (g x)
  suffices key : ∀ (y : LaurentSeries K) (hy : y ∈ E),
      g (t ⟨y,hy⟩) = t (g ⟨y,hy⟩) from key x.1 x.2
  intro y hy
  induction hy using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain ⟨z,hz,rfl⟩ := hy
    have hp := hpin ⟨z,hz⟩
    have hg := fixed_generator ⟨z,hz⟩
    have hgt := fixed_generator (τ₀ ⟨z,hz⟩)
    exact (congrArg g hp).trans (hgt.trans (hp.symm.trans (congrArg t hg.symm)))
  | algebraMap c =>
    have e : (⟨algebraMap K (LaurentSeries K) c,
        IntermediateField.algebraMap_mem E c⟩ : E) = algebraMap K E c := rfl
    have ht (a : K) : t (algebraMap K E a) = algebraMap K E a := τ.commutes a
    rw [e, ht, ga, ht]
  | add y z hy hz ihy ihz =>
    change g (t ((⟨y,hy⟩ : E) + ⟨z,hz⟩)) =
      t (g ((⟨y,hy⟩ : E) + ⟨z,hz⟩))
    rw [map_add, map_add, map_add, map_add, ihy, ihz]
  | mul y z hy hz ihy ihz =>
    change g (t ((⟨y,hy⟩ : E) * ⟨z,hz⟩)) =
      t (g ((⟨y,hy⟩ : E) * ⟨z,hz⟩))
    rw [map_mul, map_mul, map_mul, map_mul, ihy, ihz]
  | inv y hy ihy =>
    change g (t ((⟨y,hy⟩ : E)⁻¹)) = t (g ((⟨y,hy⟩ : E)⁻¹))
    rw [map_inv₀, map_inv₀, map_inv₀, map_inv₀, ihy]

/-- The field diamond commutes with arithmetic Galois on the literal Laurent
coefficient base change, by comparison on rational generators and constants. -/
theorem _root_.solution
    (d : (ZMod 25)ˣ) (σ : Gal) (x : xHFunctionFieldBar 25 H25) :
    arithmeticGalois (xHFunctionField 25 H25) σ •
      diamondAutHBar 25 H25 d x =
      diamondAutHBar 25 H25 d
        (arithmeticGalois (xHFunctionField 25 H25) σ • x) := by
  obtain ⟨γ,hγ⟩ := CohCarrier.gamma0Units_surjective 25 d⁻¹
  have hγ00 : (((γ : SL(2,ℤ)) 0 0 : ℤ) : ZMod 25) = (d : ZMod 25) := by
    have h : (((CohCarrier.gamma0Units 25 γ)⁻¹ : (ZMod 25)ˣ) : ZMod 25) =
        (((γ : SL(2,ℤ)) 0 0 : ℤ) : ZMod 25) := rfl
    rw [← h,hγ,inv_inv]
  obtain ⟨ρa,hρH,_,_,hρslash⟩ :=
    exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero ℚ 25 H25
  obtain ⟨ρ,hρeval⟩ := exists_forget_algEquiv_action
    (algebra := SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (CohCarrier.GammaH 25 H25))) ρa
  have hρH' : ∀ A : Gamma0 25, (A : SL(2,ℤ)) ∈ CohCarrier.GammaH 25 H25 →
      ρ A = 1 := by
    intro A hA
    ext y
    rw [hρeval,hρH A hA]
    rfl
  have hpin : ∀ y : xHFunctionField 25 H25,
      diamondAutHBar 25 H25 d
        ⟨coeffEmb (AlgebraicClosure ℚ) (y : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) y.2⟩ =
        (⟨coeffEmb (AlgebraicClosure ℚ) ((ρ γ y : xHFunctionField 25 H25) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ρ γ y).2⟩ : xHFunctionFieldBar 25 H25) := by
    intro y
    apply Subtype.ext
    exact diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
      25 H25 ρ hρH' (by
        intro A k f g f₁ g₁ pf pg pf₁ pg₁ c hc hf hg hf₁ hg₁ hff hgg hg0 hg₁0
        have e := congrArg (fun z : xHFunctionField 25 H25 => (z : LaurentSeries ℚ))
          (hρeval A ⟨intSeriesC ℚ pf / intSeriesC ℚ pg,
            div_mem_qExpFunctionFieldC f g hf hg hg0⟩)
        exact e.trans (hρslash A f g f₁ g₁ c hc hf hg hf₁ hg₁ hff hgg hg0 hg₁0))
      d γ hγ00 y
  exact commutes_from_rational_generators (xHFunctionField 25 H25)
    (diamondAutHBar 25 H25 d) (ρ γ) hpin σ x

end N25
