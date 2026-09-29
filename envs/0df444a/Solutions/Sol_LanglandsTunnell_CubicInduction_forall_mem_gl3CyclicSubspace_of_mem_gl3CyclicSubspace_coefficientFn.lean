-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.forall_mem_gl3CyclicSubspace_of_mem_gl3CyclicSubspace_coefficientFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/10e063b5-3654-5172-8dc1-4f97833257ae

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_compl_of_forall_le_comap_gl3AmbientRightTranslate
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_injective
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_of_mem_gl3CyclicSubspace_coefficientFn
p2m_attr_erase "instance" "LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SmoothVectors.nonarchimedeanGroup_gl2Padic FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply FLT.SmoothAdmissibleSchurCommutant.mem_repStabilizer FLT.SmoothAdmissibleSchurCommutant.mem_fixedVectors LanglandsTunnell.CubicInduction.halfModulus2_one LanglandsTunnell.CubicInduction.unipotentHom2_ofAdd LanglandsTunnell.CubicInduction.diagonal2_coe LanglandsTunnell.CubicInduction.upperUnipotent2_coe LanglandsTunnell.CubicInduction.torusChar2_one LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv FLT.SmoothVectors.coe_gl2UnipotentPadic_inv FLT.SmoothVectors.coe_gl2UnipotentPadic LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val LocalNewvector.unitValuation_apply LocalNewvector.valChar_apply FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv"

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.gl3AmbientRightTranslate CubicInduction.gl3AmbientRightTranslate_apply CubicInduction.gl3CyclicSubspace TateLocal.charExt TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 torusChar3 principalSeries3 mem_principalSeries3_iff rightTranslate_mem_principalSeries3 coefficientFn gl3Det gl3Det_ne_zero gl3Det_upperUnipotent3_mul gl3Det_diagonal3_mul charExt_units_mul eventually_charExt_eq continuous_gl3Det gl3AmbientRightTranslate gl3AmbientRightTranslate_apply gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace LocalGL3 exists_compl_of_forall_le_comap_gl3AmbientRightTranslate exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_injective exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_apply_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private def gl3DetTwist (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (f : LocalGL3 v → ℂ) : LocalGL3 v → ℂ :=
  fun g => (η (Matrix.GeneralLinearGroup.det g) : ℂ) * f g

private theorem charExt_gl3Det (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v) :
    LanglandsTunnell.TateLocal.charExt η (gl3Det v g) = (η (Matrix.GeneralLinearGroup.det g) : ℂ) := by
  rw [gl3Det, ← Matrix.GeneralLinearGroup.val_det_apply, LanglandsTunnell.TateLocal.charExt_coe_units]

private theorem gl3DetTwist_apply_eq_charExt
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (f : LocalGL3 v → ℂ) (g : LocalGL3 v) :
    gl3DetTwist v η f g = LanglandsTunnell.TateLocal.charExt η (gl3Det v g) * f g := by
  show (η (Matrix.GeneralLinearGroup.det g) : ℂ) * f g = _
  rw [charExt_gl3Det]

private theorem isLocallyConstant_charExt_gl3Det
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) :
    IsLocallyConstant fun g : LocalGL3 v => LanglandsTunnell.TateLocal.charExt η (gl3Det v g) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g => ?_
  exact ((continuous_gl3Det v).tendsto g).eventually (eventually_charExt_eq v η hη (gl3Det_ne_zero v g))

private theorem gl3DetTwist_mem_principalSeries3
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η)
    {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)} {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) :
    gl3DetTwist v η f ∈ principalSeries3 v fun i => χ i * η := by
  obtain ⟨hlc, hn, ht⟩ := mem_principalSeries3_iff.mp hf
  have hfun : gl3DetTwist v η f = fun g => LanglandsTunnell.TateLocal.charExt η (gl3Det v g) * f g :=
    funext fun g => gl3DetTwist_apply_eq_charExt v η f g
  have hlc' : IsLocallyConstant (gl3DetTwist v η f) := by
    rw [hfun]
    exact (isLocallyConstant_charExt_gl3Det v η hη).mul hlc
  refine mem_principalSeries3_iff.mpr ⟨hlc', fun x y z g => ?_, fun a g => ?_⟩
  · rw [gl3DetTwist_apply_eq_charExt, gl3DetTwist_apply_eq_charExt, gl3Det_upperUnipotent3_mul, hn]
  · have hdet : LanglandsTunnell.TateLocal.charExt η (gl3Det v (diagonal3 v a * g)) =
        (η (a 0) : ℂ) * (η (a 1) : ℂ) * (η (a 2) : ℂ) * LanglandsTunnell.TateLocal.charExt η (gl3Det v g) := by
      rw [gl3Det_diagonal3_mul, ← Units.val_mul (a 0) (a 1), ← Units.val_mul (a 0 * a 1) (a 2),
        charExt_units_mul, map_mul η (a 0 * a 1) (a 2), map_mul η (a 0) (a 1),
        Units.val_mul (η (a 0) * η (a 1)) (η (a 2)), Units.val_mul (η (a 0)) (η (a 1))]
    have htor : torusChar3 v (fun i => χ i * η) a =
        torusChar3 v χ a * ((η (a 0) : ℂ) * (η (a 1) : ℂ) * (η (a 2) : ℂ)) := by
      simp only [torusChar3, MonoidHom.mul_apply, Units.val_mul, Fin.prod_univ_three]
      ring
    rw [gl3DetTwist_apply_eq_charExt, gl3DetTwist_apply_eq_charExt, hdet, ht a g, htor]
    ring

private theorem gl3DetTwist_inv_gl3DetTwist
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (f : LocalGL3 v → ℂ) : gl3DetTwist v η⁻¹ (gl3DetTwist v η f) = f := by
  funext g
  simp only [gl3DetTwist, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

private theorem gl3DetTwist_gl3DetTwist_inv
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (f : LocalGL3 v → ℂ) : gl3DetTwist v η (gl3DetTwist v η⁻¹ f) = f := by
  funext g
  simp only [gl3DetTwist, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]

private def principalSeries3TwistEquiv
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    principalSeries3 v χ ≃ₗ[ℂ] principalSeries3 v fun i => χ i * η where
  toFun f := ⟨gl3DetTwist v η f, gl3DetTwist_mem_principalSeries3 v η hη f.2⟩
  invFun f := ⟨gl3DetTwist v η⁻¹ f, by
    have hη' : IsLocallyConstant η⁻¹ := hη.inv
    have h := gl3DetTwist_mem_principalSeries3 v η⁻¹ hη' f.2
    have e : (fun i => χ i * η * η⁻¹) = χ := funext fun i => mul_inv_cancel_right (χ i) η
    exact (congrArg (fun χ' => gl3DetTwist v η⁻¹ (f : LocalGL3 v → ℂ) ∈ principalSeries3 v χ') e).mp h⟩
  map_add' f f' := Subtype.ext (funext fun g =>
    mul_add (η (Matrix.GeneralLinearGroup.det g) : ℂ) ((f : LocalGL3 v → ℂ) g) ((f' : LocalGL3 v → ℂ) g))
  map_smul' c f := Subtype.ext (funext fun g =>
    mul_left_comm (η (Matrix.GeneralLinearGroup.det g) : ℂ) c ((f : LocalGL3 v → ℂ) g))
  left_inv f := Subtype.ext (gl3DetTwist_inv_gl3DetTwist v η f)
  right_inv f := Subtype.ext (gl3DetTwist_gl3DetTwist_inv v η f)

private theorem principalSeries3TwistEquiv_apply_coe
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : ↥(principalSeries3 v χ)) :
    (principalSeries3TwistEquiv v η hη χ f : LocalGL3 v → ℂ) = gl3DetTwist v η f :=
  rfl

private theorem gl3AmbientRightTranslate_gl3DetTwist
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v) (f : LocalGL3 v → ℂ) :
    gl3AmbientRightTranslate (R := ℂ) g (gl3DetTwist v η f) =
      (η (Matrix.GeneralLinearGroup.det g) : ℂ) • gl3DetTwist v η (gl3AmbientRightTranslate (R := ℂ) g f) := by
  funext h
  simp only [gl3AmbientRightTranslate_apply, gl3DetTwist, map_mul, Units.val_mul, Pi.smul_apply, smul_eq_mul]
  ring

private theorem coefficientFn_principalSeries3TwistEquiv
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : IsLocallyConstant η) {χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)}
    (L : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)) :
    coefficientFn (L ∘ₗ (principalSeries3TwistEquiv v η hη χ).symm.toLinearMap)
        (principalSeries3TwistEquiv v η hη χ f) =
      gl3DetTwist v η (coefficientFn L f) := by
  funext g
  have key : (⟨gl3AmbientRightTranslate (R := ℂ) g (principalSeries3TwistEquiv v η hη χ f : LocalGL3 v → ℂ),
        rightTranslate_mem_principalSeries3 (principalSeries3TwistEquiv v η hη χ f).2 g⟩ :
          ↥(principalSeries3 v fun i => χ i * η)) =
      (η (Matrix.GeneralLinearGroup.det g) : ℂ) • principalSeries3TwistEquiv v η hη χ
        ⟨gl3AmbientRightTranslate (R := ℂ) g (f : LocalGL3 v → ℂ), rightTranslate_mem_principalSeries3 f.2 g⟩ := by
    apply Subtype.ext
    show gl3AmbientRightTranslate (R := ℂ) g (principalSeries3TwistEquiv v η hη χ f : LocalGL3 v → ℂ) =
      (η (Matrix.GeneralLinearGroup.det g) : ℂ) • (principalSeries3TwistEquiv v η hη χ
        ⟨gl3AmbientRightTranslate (R := ℂ) g (f : LocalGL3 v → ℂ), rightTranslate_mem_principalSeries3 f.2 g⟩ :
          LocalGL3 v → ℂ)
    rw [principalSeries3TwistEquiv_apply_coe, principalSeries3TwistEquiv_apply_coe]
    exact gl3AmbientRightTranslate_gl3DetTwist v η g f
  show L ((principalSeries3TwistEquiv v η hη χ).symm
      ⟨gl3AmbientRightTranslate (R := ℂ) g (principalSeries3TwistEquiv v η hη χ f : LocalGL3 v → ℂ),
        rightTranslate_mem_principalSeries3 (principalSeries3TwistEquiv v η hη χ f).2 g⟩) =
    (η (Matrix.GeneralLinearGroup.det g) : ℂ) *
      L ⟨gl3AmbientRightTranslate (R := ℂ) g (f : LocalGL3 v → ℂ), rightTranslate_mem_principalSeries3 f.2 g⟩
  rw [key, map_smul, LinearEquiv.symm_apply_apply, map_smul, smul_eq_mul]

end LanglandsTunnell.CubicInduction

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "CubicInduction.gl3AmbientRightTranslate CubicInduction.gl3AmbientRightTranslate_apply CubicInduction.gl3CyclicSubspace TateLocal.charExt TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 torusChar3 principalSeries3 mem_principalSeries3_iff rightTranslate_mem_principalSeries3 coefficientFn gl3Det gl3Det_ne_zero gl3Det_upperUnipotent3_mul gl3Det_diagonal3_mul charExt_units_mul eventually_charExt_eq continuous_gl3Det gl3AmbientRightTranslate gl3AmbientRightTranslate_apply gl3CyclicSubspace gl3AmbientRightTranslate_mem_gl3CyclicSubspace LocalGL3 exists_compl_of_forall_le_comap_gl3AmbientRightTranslate exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_injective exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_apply_eq"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem linearMap_eq_zero_of_genEigen {k V V' : Type*} [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    (f : Module.End k V) (g : Module.End k V') (a b : k) (n : ℕ)
    (hV : ∀ v : V, ((f - a • (1 : Module.End k V)) ^ n) v = 0)
    (hV' : ∀ v' : V', g v' = b • v')
    (hab : a ≠ b)
    (φ : V →ₗ[k] V') (hφ : ∀ v : V, φ (f v) = g (φ v)) : φ = 0 := by
  have step : ∀ w : V, φ ((f - a • (1 : Module.End k V)) w) = (b - a) • φ w := by
    intro w
    simp [hφ, hV', sub_smul]
  have key : ∀ m : ℕ, ∀ v : V, φ (((f - a • (1 : Module.End k V)) ^ m) v) = (b - a) ^ m • φ v := by
    intro m
    induction m with
    | zero => intro v; simp
    | succ m ih =>
      intro v
      simp only [pow_succ, Module.End.mul_apply, ih, step, smul_smul]
  have hne : (b - a) ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hab.symm)
  ext v
  have h := key n v
  rw [hV v, map_zero] at h
  simpa [hne] using h.symm

private theorem exists_isCompl_of_commute {k V T : Type*} [Field k] [AddCommGroup V] [Module k V]
    [CommMonoid T] (ρ : T →* Module.End k V) (V₁ : Submodule k V) (χ χ' : T → k)
    (h₁ : ∀ t : T, ∀ v ∈ V₁, ρ t v = χ t • v)
    (h₂ : ∀ (t : T) (v : V), ρ t v - χ' t • v ∈ V₁)
    (hsep : ∃ t₀ : T, χ t₀ ≠ χ' t₀) :
    ∃ V₂ : Submodule k V, (∀ t : T, ∀ v ∈ V₂, ρ t v ∈ V₂) ∧ V₁ ⊓ V₂ = ⊥ ∧ V₁ ⊔ V₂ = ⊤ ∧
      ∀ t : T, ∀ v ∈ V₂, ρ t v = χ' t • v := by
  obtain ⟨t₀, ht₀⟩ := hsep
  have hd : χ t₀ - χ' t₀ ≠ 0 := sub_ne_zero.mpr ht₀

  set P : Module.End k V := (χ t₀ - χ' t₀)⁻¹ • (ρ t₀ - χ' t₀ • (1 : Module.End k V)) with hP
  have hP_apply : ∀ v : V, P v = (χ t₀ - χ' t₀)⁻¹ • (ρ t₀ v - χ' t₀ • v) := by
    intro v
    simp [hP]
  have hP_mem : ∀ v : V, P v ∈ V₁ := by
    intro v
    rw [hP_apply]
    exact V₁.smul_mem _ (h₂ t₀ v)
  have hP_fix : ∀ v ∈ V₁, P v = v := by
    intro v hv
    rw [hP_apply, h₁ t₀ v hv, ← sub_smul, smul_smul, inv_mul_cancel₀ hd, one_smul]
  have hP_comm : ∀ (t : T) (v : V), P (ρ t v) = ρ t (P v) := by
    intro t v
    have hsw : ρ t₀ (ρ t v) = ρ t (ρ t₀ v) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
    rw [hP_apply, hP_apply, map_smul, map_sub, map_smul, hsw]
  have hinf : V₁ ⊓ LinearMap.ker P = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hv
    rw [Submodule.mem_bot]
    calc v = P v := (hP_fix v hv.1).symm
      _ = 0 := hv.2
  refine ⟨LinearMap.ker P, ?_, hinf, ?_, ?_⟩
  · intro t v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hP_comm, hv, map_zero]
  · rw [eq_top_iff]
    intro v _
    have hker : v - P v ∈ LinearMap.ker P := by
      rw [LinearMap.mem_ker, map_sub, hP_fix (P v) (hP_mem v), sub_self]
    simpa using Submodule.add_mem_sup (hP_mem v) hker
  · intro t v hv
    have hker : ρ t v - χ' t • v ∈ LinearMap.ker P := by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [map_sub, map_smul, hP_comm, hv, map_zero, smul_zero, sub_zero]
    have hboth : ρ t v - χ' t • v ∈ V₁ ⊓ LinearMap.ker P := Submodule.mem_inf.mpr ⟨h₂ t v, hker⟩
    rw [hinf, Submodule.mem_bot] at hboth
    exact sub_eq_zero.mp hboth

private theorem isSimpleModule_of_forall_end_eq_smul
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [Nontrivial M]
    (hss : ∀ N : Submodule A M, ∃ N' : Submodule A M, N ⊓ N' = ⊥ ∧ N ⊔ N' = ⊤)
    (hend : ∀ φ : M →ₗ[A] M, ∃ c : k, ∀ m : M, φ m = c • m) :
    IsSimpleModule A M := by
  refine (isSimpleModule_iff A M).mpr (IsSimpleOrder.of_forall_eq_top fun N hN => ?_)
  obtain ⟨N', hinf, hsup⟩ := hss N
  have hc : IsCompl N N' := isCompl_iff.mpr ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
  set e : M →ₗ[A] M := N.subtype ∘ₗ Submodule.projectionOnto N N' hc with he
  obtain ⟨c, hce⟩ := hend e
  obtain ⟨y, hy0⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hN)
  have hfix : e y = y := by
    rw [he, LinearMap.comp_apply, Submodule.projectionOnto_apply_left, Submodule.subtype_apply]
  have hc1 : c = 1 := by
    have h1 : (c - 1) • (y : M) = 0 := by rw [sub_smul, one_smul, ← hce y, hfix, sub_self]
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact sub_eq_zero.mp h2
    · exact absurd ((Submodule.coe_eq_zero).mp h2) hy0
  refine Submodule.eq_top_iff'.mpr fun m => ?_
  have hm : e m = m := by rw [hce m, hc1, one_smul]
  rw [← hm, he, LinearMap.comp_apply]
  exact Submodule.coe_mem _

private theorem finrank_linearMap_le
    {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
    {M : Type*} [AddCommGroup M] [Module A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
    (M₁ : Submodule A M)
    [FiniteDimensional k (M₁ →ₗ[A] N)] [FiniteDimensional k ((M ⧸ M₁) →ₗ[A] N)] :
    FiniteDimensional k (M →ₗ[A] N) ∧
      Module.finrank k (M →ₗ[A] N) ≤
        Module.finrank k (M₁ →ₗ[A] N) + Module.finrank k ((M ⧸ M₁) →ₗ[A] N) := by
  let r : (M →ₗ[A] N) →ₗ[k] (M₁ →ₗ[A] N) :=
    { toFun := fun f => f ∘ₗ M₁.subtype
      map_add' := fun f g => LinearMap.add_comp _ _ _
      map_smul' := fun c f => LinearMap.smul_comp _ _ _ }
  let q : ((M ⧸ M₁) →ₗ[A] N) →ₗ[k] (M →ₗ[A] N) :=
    { toFun := fun g => g ∘ₗ M₁.mkQ
      map_add' := fun f g => LinearMap.add_comp _ _ _
      map_smul' := fun c f => LinearMap.smul_comp _ _ _ }
  have hle : LinearMap.ker r ≤ LinearMap.range q := by
    intro f hf
    have h0 : f ∘ₗ M₁.subtype = 0 := LinearMap.mem_ker.mp hf
    have hM₁ : M₁ ≤ LinearMap.ker f := LinearMap.le_ker_iff_comp_subtype_eq_zero.mpr h0
    exact LinearMap.mem_range.mpr ⟨M₁.liftQ f hM₁, M₁.liftQ_mkQ f hM₁⟩
  have hker : FiniteDimensional k (LinearMap.ker r) := Submodule.finiteDimensional_of_le hle
  have hfin : FiniteDimensional k (M →ₗ[A] N) := by
    refine Module.finite_def.mpr (Submodule.fg_of_fg_map_of_fg_inf_ker r ?_ ?_)
    · exact IsNoetherian.noetherian _
    · rw [top_inf_eq]
      exact (Submodule.fg_top _).mp (Module.finite_def.mp hker)
  refine ⟨hfin, ?_⟩
  calc Module.finrank k (M →ₗ[A] N)
      = Module.finrank k (LinearMap.range r) + Module.finrank k (LinearMap.ker r) :=
        (LinearMap.finrank_range_add_finrank_ker r).symm
    _ ≤ Module.finrank k (M₁ →ₗ[A] N) + Module.finrank k (LinearMap.range q) :=
        add_le_add (Submodule.finrank_le _) (Submodule.finrank_mono hle)
    _ ≤ Module.finrank k (M₁ →ₗ[A] N) + Module.finrank k ((M ⧸ M₁) →ₗ[A] N) :=
        Nat.add_le_add_left (LinearMap.finrank_range_le q) _

private def twistFn {F : Type*} [Field F] {R : Type*} [CommRing R]
    (m : GL (Fin 3) F → Rˣ) (W : GL (Fin 3) F → R) : GL (Fin 3) F → R :=
  fun g => (m g : R) * W g

private def gl3TwistEnd {F : Type*} [Field F] {R : Type*} [CommRing R]
    (m : GL (Fin 3) F → Rˣ) : Module.End R (GL (Fin 3) F → R) where
  toFun := twistFn m
  map_add' W W' := funext fun g => by
    simp only [twistFn, Pi.add_apply]
    exact mul_add _ _ _
  map_smul' c W := funext fun g => by
    simp only [twistFn, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_left_comm _ _ _

private theorem gl3TwistEnd_apply {F : Type*} [Field F] {R : Type*} [CommRing R]
    (m : GL (Fin 3) F → Rˣ) (W : GL (Fin 3) F → R) : gl3TwistEnd m W = twistFn m W := rfl

private theorem gl3AmbientRightTranslate_twistFn {F : Type*} [Field F] {R : Type*} [CommRing R]
    (m : GL (Fin 3) F → Rˣ) (hm : ∀ g h, m (g * h) = m g * m h)
    (g : GL (Fin 3) F) (W : GL (Fin 3) F → R) :
    LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate (R := R) g (twistFn m W) =
      (m g : R) • twistFn m
        (LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate (R := R) g W) := by
  funext h
  simp only [LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate_apply, twistFn, hm,
    Units.val_mul, Pi.smul_apply, smul_eq_mul]
  ring

private theorem map_gl3TwistEnd_gl3CyclicSubspace {F : Type*} [Field F] {R : Type*} [CommRing R]
    (m : GL (Fin 3) F → Rˣ) (hm : ∀ g h, m (g * h) = m g * m h) (W : GL (Fin 3) F → R) :
    (LanglandsTunnell.CubicInduction.gl3CyclicSubspace W).map (gl3TwistEnd m) =
      LanglandsTunnell.CubicInduction.gl3CyclicSubspace (twistFn m W) := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, gl3TwistEnd_apply]
    have key : twistFn m (LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate (R := R) h W) =
        ((m h)⁻¹ : Rˣ).val •
          LanglandsTunnell.CubicInduction.gl3AmbientRightTranslate (R := R) h (twistFn m W) := by
      rw [gl3AmbientRightTranslate_twistFn m hm, ← mul_smul, Units.inv_mul, one_smul]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    simp only [SetLike.mem_coe]
    rw [gl3AmbientRightTranslate_twistFn m hm, ← gl3TwistEnd_apply, ← map_smul]
    exact Submodule.mem_map_of_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩))

private theorem forall_mem_gl3CyclicSubspace_twistFn {F : Type*} [Field F] {R : Type*}
    [CommRing R] (m : GL (Fin 3) F → Rˣ) (hm : ∀ g h, m (g * h) = m g * m h)
    (W : GL (Fin 3) F → R)
    (hW : ∀ W' ∈ LanglandsTunnell.CubicInduction.gl3CyclicSubspace W, W' ≠ 0 →
      W ∈ LanglandsTunnell.CubicInduction.gl3CyclicSubspace W') :
    ∀ W' ∈ LanglandsTunnell.CubicInduction.gl3CyclicSubspace (twistFn m W), W' ≠ 0 →
      twistFn m W ∈ LanglandsTunnell.CubicInduction.gl3CyclicSubspace W' := by
  intro W' hW' hne
  rw [← map_gl3TwistEnd_gl3CyclicSubspace m hm W] at hW'
  obtain ⟨W₀, hW₀, rfl⟩ := Submodule.mem_map.mp hW'
  rw [gl3TwistEnd_apply] at hne ⊢
  have hne₀ : W₀ ≠ 0 := by
    rintro rfl
    exact hne (funext fun g => by simp only [twistFn, Pi.zero_apply, mul_zero])
  have hgen := hW W₀ hW₀ hne₀
  have hmem : gl3TwistEnd m W ∈
      (LanglandsTunnell.CubicInduction.gl3CyclicSubspace W₀).map (gl3TwistEnd m) :=
    Submodule.mem_map_of_mem hgen
  rwa [map_gl3TwistEnd_gl3CyclicSubspace m hm W₀, gl3TwistEnd_apply] at hmem

universe u₁ u₂ u₃

section Transport

open Matrix

variable {F : Type u₁} [CommRing F] {R : Type u₂} [CommRing R] {V : Type u₃} [AddCommGroup V] [Module R V]

private def coeffFn (π : GL (Fin 3) F →* Module.End R V) (L : V →ₗ[R] R) : V →ₗ[R] (GL (Fin 3) F → R) where
  toFun u := fun g => L (π g u)
  map_add' u₁ u₂ := by
    funext g
    simp only [map_add, Pi.add_apply]
  map_smul' c u := by
    funext g
    simp only [map_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply]

private theorem coeffFn_apply (π : GL (Fin 3) F →* Module.End R V) (L : V →ₗ[R] R) (u : V) (g : GL (Fin 3) F) :
    coeffFn π L u g = L (π g u) := rfl

private theorem gl3AmbientRightTranslate_coeffFn (π : GL (Fin 3) F →* Module.End R V) (L : V →ₗ[R] R)
    (h : GL (Fin 3) F) (u : V) :
    gl3AmbientRightTranslate (R := R) h (coeffFn π L u) = coeffFn π L (π h u) := by
  funext g
  rw [gl3AmbientRightTranslate_apply, coeffFn_apply, coeffFn_apply, map_mul, Module.End.mul_apply]

private theorem map_coeffFn_span_range (π : GL (Fin 3) F →* Module.End R V) (L : V →ₗ[R] R) (u : V) :
    (Submodule.span R (Set.range fun h : GL (Fin 3) F => π h u)).map (coeffFn π L) =
      gl3CyclicSubspace (coeffFn π L u) := by
  have hfun : (⇑(coeffFn π L) ∘ fun h : GL (Fin 3) F => π h u) =
      fun h : GL (Fin 3) F => gl3AmbientRightTranslate (R := R) h (coeffFn π L u) :=
    funext fun h => (gl3AmbientRightTranslate_coeffFn π L h u).symm
  rw [Submodule.map_span, gl3CyclicSubspace, ← Set.range_comp, hfun]

private theorem coeffFn_mem_gl3CyclicSubspace_of_forall_span_eq_top (π : GL (Fin 3) F →* Module.End R V)
    (L : V →ₗ[R] R) (w : V)
    (hirr : ∀ u : V, u ≠ 0 → Submodule.span R (Set.range fun h : GL (Fin 3) F => π h u) = ⊤) :
    ∀ G ∈ gl3CyclicSubspace (coeffFn π L w), G ≠ 0 → coeffFn π L w ∈ gl3CyclicSubspace G := by
  intro G hG hG0
  rw [← map_coeffFn_span_range] at hG
  obtain ⟨u, -, rfl⟩ := Submodule.mem_map.mp hG
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hG0 (map_zero _)
  rw [← map_coeffFn_span_range, hirr u hu0, Submodule.map_top]
  exact LinearMap.mem_range_self _ w

end Transport

section Descent

open Matrix

variable {F : Type u₁} [CommRing F] {R : Type u₂} [CommRing R]

private theorem gl3CyclicSubspace_le_of_mem {X W : GL (Fin 3) F → R} (hW : W ∈ gl3CyclicSubspace X) :
    gl3CyclicSubspace W ≤ gl3CyclicSubspace X := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨h, rfl⟩
  exact gl3AmbientRightTranslate_mem_gl3CyclicSubspace X h hW

private theorem forall_mem_gl3CyclicSubspace_of_mem {X W : GL (Fin 3) F → R}
    (hX : ∀ G ∈ gl3CyclicSubspace X, G ≠ 0 → X ∈ gl3CyclicSubspace G) (hW : W ∈ gl3CyclicSubspace X) :
    ∀ G ∈ gl3CyclicSubspace W, G ≠ 0 → W ∈ gl3CyclicSubspace G := by
  intro G hG hG0
  have hGX : G ∈ gl3CyclicSubspace X := gl3CyclicSubspace_le_of_mem hW hG
  have hXG : X ∈ gl3CyclicSubspace G := hX G hGX hG0
  exact gl3CyclicSubspace_le_of_mem hXG hW

end Descent

section Wall

variable (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))

private def principalSeriesRep3 : LocalGL3 v →* Module.End ℂ ↥(principalSeries3 v χ) where
  toFun g := (gl3AmbientRightTranslate (R := ℂ) g).restrict (fun _ hf => rightTranslate_mem_principalSeries3 hf g)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext h
    show (f : LocalGL3 v → ℂ) (h * 1) = (f : LocalGL3 v → ℂ) h
    rw [mul_one]
  map_mul' g₁ g₂ := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext h
    show (f : LocalGL3 v → ℂ) (h * (g₁ * g₂)) = (f : LocalGL3 v → ℂ) (h * g₁ * g₂)
    rw [mul_assoc]

private theorem principalSeriesRep3_apply_coe (h : LocalGL3 v) (u : ↥(principalSeries3 v χ)) :
    ((principalSeriesRep3 v χ h u : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ) =
      gl3AmbientRightTranslate (R := ℂ) h (u : LocalGL3 v → ℂ) := rfl

private theorem coefficientFn_eq_coeffFn (L : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)) :
    coefficientFn L f = coeffFn (principalSeriesRep3 v χ) L f := rfl

private theorem span_range_rep_eq_top_of_compl_of_end
    (hcompl : ∀ U : Submodule ℂ (LocalGL3 v → ℂ), U ≤ principalSeries3 v χ →
      (∀ g : LocalGL3 v, U ≤ U.comap (gl3AmbientRightTranslate (R := ℂ) g)) →
      ∃ U' : Submodule ℂ (LocalGL3 v → ℂ), U' ≤ principalSeries3 v χ ∧
        (∀ g : LocalGL3 v, U' ≤ U'.comap (gl3AmbientRightTranslate (R := ℂ) g)) ∧
        U ⊓ U' = ⊥ ∧ U ⊔ U' = principalSeries3 v χ)
    (hend : ∀ T : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ),
      (∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
        (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
          gl3AmbientRightTranslate (R := ℂ) g (T f)) →
      ∃ c : ℂ, T = c • LinearMap.id) :
    ∀ u : ↥(principalSeries3 v χ), u ≠ 0 →
      Submodule.span ℂ (Set.range fun h : LocalGL3 v => principalSeriesRep3 v χ h u) = ⊤ := by
  intro u hu
  set S : Submodule ℂ ↥(principalSeries3 v χ) :=
    Submodule.span ℂ (Set.range fun h : LocalGL3 v => principalSeriesRep3 v χ h u) with hS
  have hS_stable : ∀ g : LocalGL3 v, ∀ s ∈ S, principalSeriesRep3 v χ g s ∈ S := by
    intro g s hs
    refine Submodule.span_induction (p := fun s _ => principalSeriesRep3 v χ g s ∈ S) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨h, rfl⟩
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    · show principalSeriesRep3 v χ g 0 ∈ S
      rw [map_zero]
      exact S.zero_mem
    · intro s₁ s₂ _ _ h₁ h₂
      rw [map_add]
      exact S.add_mem h₁ h₂
    · intro c s _ h
      rw [map_smul]
      exact S.smul_mem c h
  set U : Submodule ℂ (LocalGL3 v → ℂ) := S.map (principalSeries3 v χ).subtype with hU
  have hU_le : U ≤ principalSeries3 v χ := by
    intro x hx
    obtain ⟨s, -, rfl⟩ := Submodule.mem_map.mp hx
    exact s.2
  have hU_stable : ∀ g : LocalGL3 v, U ≤ U.comap (gl3AmbientRightTranslate (R := ℂ) g) := by
    intro g x hx
    obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨principalSeriesRep3 v χ g s, hS_stable g s hs, rfl⟩)
  obtain ⟨U', hU'_le, hU'_stable, hinf, hsup⟩ := hcompl U hU_le hU_stable
  set S' : Submodule ℂ ↥(principalSeries3 v χ) := U'.comap (principalSeries3 v χ).subtype with hS'
  have hS'_stable : ∀ g : LocalGL3 v, ∀ s ∈ S', principalSeriesRep3 v χ g s ∈ S' := by
    intro g s hs
    exact Submodule.mem_comap.mpr (Submodule.mem_comap.mp (hU'_stable g (Submodule.mem_comap.mp hs)))
  have hSS'_inf : S ⊓ S' = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro s hs
    obtain ⟨hs₁, hs₂⟩ := Submodule.mem_inf.mp hs
    have h1 : (s : LocalGL3 v → ℂ) ∈ U ⊓ U' :=
      Submodule.mem_inf.mpr ⟨Submodule.mem_map.mpr ⟨s, hs₁, rfl⟩, Submodule.mem_comap.mp hs₂⟩
    rw [hinf, Submodule.mem_bot] at h1
    exact Subtype.ext h1
  have hSS'_sup : S ⊔ S' = ⊤ := by
    rw [eq_top_iff]
    rintro s -
    have h1 : (s : LocalGL3 v → ℂ) ∈ U ⊔ U' := by
      rw [hsup]
      exact s.2
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
    obtain ⟨a₀, ha₀, rfl⟩ := Submodule.mem_map.mp ha
    have hb_mem : b ∈ principalSeries3 v χ := hU'_le hb
    have hs_eq : s = a₀ + ⟨b, hb_mem⟩ := by
      apply Subtype.ext
      exact hab.symm
    rw [hs_eq]
    exact Submodule.mem_sup.mpr ⟨a₀, ha₀, ⟨b, hb_mem⟩, Submodule.mem_comap.mpr hb, rfl⟩
  have hcompl' : IsCompl S S' := IsCompl.of_eq hSS'_inf hSS'_sup
  set T : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ) := S.projection S' hcompl' with hT
  have hT_left : ∀ s ∈ S, T s = s := fun s hs => Submodule.projection_apply_left hcompl' ⟨s, hs⟩
  have hT_right : ∀ s ∈ S', T s = 0 := fun s hs => Submodule.projection_apply_of_mem_right hcompl' hs
  have hT_comm : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
      T (principalSeriesRep3 v χ g f) = principalSeriesRep3 v χ g (T f) := by
    intro g f
    have hf : f ∈ S ⊔ S' := by
      rw [hSS'_sup]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
    simp only [map_add, hT_left a ha, hT_right b hb, hT_left _ (hS_stable g a ha),
      hT_right _ (hS'_stable g b hb), add_zero]
  have hT_comm' : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
      (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (T f) :=
    fun g f => congrArg Subtype.val (hT_comm g f)
  obtain ⟨c, hc⟩ := hend T hT_comm'
  have hc_one : c = 1 := by
    have hu_mem : u ∈ S :=
      Submodule.subset_span ⟨1, by show principalSeriesRep3 v χ 1 u = u; rw [map_one, Module.End.one_apply]⟩
    have h1 : c • u = u := by
      have h := hT_left u hu_mem
      rwa [hc, LinearMap.smul_apply, LinearMap.id_apply] at h
    have h2 : (c - 1) • u = 0 := (sub_smul c 1 u).trans (by rw [one_smul]; exact sub_eq_zero.mpr h1)
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hu
  have hS'_bot : S' = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro s hs
    have h1 : T s = 0 := hT_right s hs
    have h3 : T s = c • s := by simp only [hc, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hc_one] at h3
    exact (one_smul ℂ s).symm.trans (h3.symm.trans h1)
  rw [hS'_bot, sup_bot_eq] at hSS'_sup
  exact hSS'_sup

private def HasScalarCommutant : Prop :=
  ∀ T : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ),
    (∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
      (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (T f)) →
    ∃ c : ℂ, T = c • LinearMap.id

private theorem hasScalarCommutant_of_three_types
    (hreg : Function.Injective χ → HasScalarCommutant v χ)
    (htwo : ¬ Function.Injective χ → ¬ (χ 0 = χ 1 ∧ χ 1 = χ 2) → HasScalarCommutant v χ)
    (hall : (χ 0 = χ 1 ∧ χ 1 = χ 2) → HasScalarCommutant v χ) :
    HasScalarCommutant v χ := by
  by_cases hinj : Function.Injective χ
  · exact hreg hinj
  · by_cases hconst : χ 0 = χ 1 ∧ χ 1 = χ 2
    · exact hall hconst
    · exact htwo hinj hconst

private theorem span_range_rep_eq_top_of_rows
    (hcompl : ∀ U : Submodule ℂ (LocalGL3 v → ℂ), U ≤ principalSeries3 v χ →
      (∀ g : LocalGL3 v, U ≤ U.comap (gl3AmbientRightTranslate (R := ℂ) g)) →
      ∃ U' : Submodule ℂ (LocalGL3 v → ℂ), U' ≤ principalSeries3 v χ ∧
        (∀ g : LocalGL3 v, U' ≤ U'.comap (gl3AmbientRightTranslate (R := ℂ) g)) ∧
        U ⊓ U' = ⊥ ∧ U ⊔ U' = principalSeries3 v χ)
    (hreg : Function.Injective χ → HasScalarCommutant v χ)
    (htwo : ¬ Function.Injective χ → ¬ (χ 0 = χ 1 ∧ χ 1 = χ 2) → HasScalarCommutant v χ)
    (hall : (χ 0 = χ 1 ∧ χ 1 = χ 2) → HasScalarCommutant v χ) :
    ∀ u : ↥(principalSeries3 v χ), u ≠ 0 →
      Submodule.span ℂ (Set.range fun h : LocalGL3 v => principalSeriesRep3 v χ h u) = ⊤ :=
  span_range_rep_eq_top_of_compl_of_end v χ hcompl (hasScalarCommutant_of_three_types v χ hreg htwo hall)

private theorem span_range_rep_eq_top_of_unit
    (hunit : ∀ i, ∀ x : (v.adicCompletion ℚ)ˣ, ‖((χ i x : ℂˣ) : ℂ)‖ = 1) :
    ∀ u : ↥(principalSeries3 v χ), u ≠ 0 →
      Submodule.span ℂ (Set.range fun h : LocalGL3 v => principalSeriesRep3 v χ h u) = ⊤ := by
  refine span_range_rep_eq_top_of_rows v χ ?_ ?_ ?_ ?_
  · intro U hU hstab
    exact exists_compl_of_forall_le_comap_gl3AmbientRightTranslate v χ hunit U hU hstab
  · intro hreg T hT
    exact exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_injective v χ hreg T hT
  · intro htwo hne T hT
    exact exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_not_injective v χ hunit htwo hne T hT
  · intro hall T hT
    exact exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_apply_eq v χ hall T hT

end Wall

end LanglandsTunnell.CubicInduction

p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_of_mem_gl3CyclicSubspace_coefficientFn.LanglandsTunnell.CubicInduction"

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hunit : ∀ i, ∀ x : (v.adicCompletion ℚ)ˣ, ‖((χ i x : ℂˣ) : ℂ)‖ = 1)
    (L : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ) (f : ↥(principalSeries3 v χ)) (W : LocalGL3 v → ℂ)
    (hW : W ∈ gl3CyclicSubspace (coefficientFn L f)) :
    ∀ F ∈ gl3CyclicSubspace W, F ≠ 0 → W ∈ gl3CyclicSubspace F := by
  have hX : ∀ G ∈ gl3CyclicSubspace (coeffFn (principalSeriesRep3 v χ) L f), G ≠ 0 →
      coeffFn (principalSeriesRep3 v χ) L f ∈ gl3CyclicSubspace G :=
    coeffFn_mem_gl3CyclicSubspace_of_forall_span_eq_top (principalSeriesRep3 v χ) L f
      (span_range_rep_eq_top_of_unit v χ hunit)
  rw [← coefficientFn_eq_coeffFn] at hX
  exact forall_mem_gl3CyclicSubspace_of_mem hX hW

end

end S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_of_mem_gl3CyclicSubspace_coefficientFn
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_forall_mem_gl3CyclicSubspace_of_mem_gl3CyclicSubspace_coefficientFn (solution)
