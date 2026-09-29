-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c47e8416-4d36-5dd5-a592-ef42f600eaee

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Theorems.Thm_LanglandsTunnell_CubicInduction_card_le_one_of_linearIndependent_of_upperUnipotent3_of_diagonal3_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_apply_eq
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.translateRepStep_apply_coe LanglandsTunnell.CubicInduction.translateFn_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_apply_eq.LanglandsTunnell.CubicInduction"

section

open Matrix Filter Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Det gl3Det_ne_zero gl3Det_upperUnipotent3_mul gl3Det_diagonal3_mul cellSection charExt_units_mul cellSection_ne_zero eventually_norm_eq eventually_charExt_eq continuous_gl3Det cellSection_mem_principalSeries3 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 LocalGL3 card_le_one_of_linearIndependent_of_upperUnipotent3_of_diagonal3_one"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem continuous_diagonal3 : Continuous (diagonal3 v) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_pi fun i : Fin 3 => Units.continuous_val.comp (continuous_apply i)).matrix_diagonal
  · exact (continuous_pi fun i : Fin 3 => Units.continuous_coe_inv.comp (continuous_apply i)).matrix_diagonal

private theorem halfModulus3_ne_zero (a : Fin 3 → (v.adicCompletion ℚ)ˣ) : halfModulus3 v a ≠ 0 := by
  simp [halfModulus3, (a 0).ne_zero, (a 2).ne_zero]

private theorem isLocallyConstant_halfModulus3 : IsLocallyConstant (halfModulus3 v) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro a

  have hc0 : Continuous fun b : Fin 3 → (v.adicCompletion ℚ)ˣ => (b 0 : v.adicCompletion ℚ) :=
    Units.continuous_val.comp (continuous_apply (0 : Fin 3))
  have hc2 : Continuous fun b : Fin 3 → (v.adicCompletion ℚ)ˣ => (b 2 : v.adicCompletion ℚ) :=
    Units.continuous_val.comp (continuous_apply (2 : Fin 3))
  have h0 : ∀ᶠ b : Fin 3 → (v.adicCompletion ℚ)ˣ in 𝓝 a,
      ‖(b 0 : v.adicCompletion ℚ)‖ = ‖(a 0 : v.adicCompletion ℚ)‖ :=
    (hc0.continuousAt (x := a)).eventually (eventually_norm_eq v (a 0).ne_zero)
  have h2 : ∀ᶠ b : Fin 3 → (v.adicCompletion ℚ)ˣ in 𝓝 a,
      ‖(b 2 : v.adicCompletion ℚ)‖ = ‖(a 2 : v.adicCompletion ℚ)‖ :=
    (hc2.continuousAt (x := a)).eventually (eventually_norm_eq v (a 2).ne_zero)
  filter_upwards [h0, h2] with b hb0 hb2
  simp only [halfModulus3, Function.comp_apply, hb0, hb2]

private theorem torusChar3_update_one (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (i : Fin 3)
    (u : (v.adicCompletion ℚ)ˣ) :
    torusChar3 v χ (Function.update (1 : Fin 3 → (v.adicCompletion ℚ)ˣ) i u) = ((χ i u : ℂˣ) : ℂ) := by
  unfold torusChar3
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Function.update_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem isLocallyConstant_of_mem_principalSeries3_of_ne_zero
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : LocalGL3 v → ℂ) (i : Fin 3) :
    f ∈ principalSeries3 v χ → f ≠ 0 → IsLocallyConstant (χ i) := by
  intro hf hne
  obtain ⟨g, hg⟩ := Function.ne_iff.1 hne
  have hg' : f g ≠ 0 := hg
  have hF : IsLocallyConstant fun a : Fin 3 → (v.adicCompletion ℚ)ˣ => f (diagonal3 v a * g) :=
    (isLocallyConstant_of_mem_principalSeries3 hf).comp_continuous
      ((continuous_diagonal3 v).mul continuous_const)
  simp_rw [apply_diagonal3_mul_of_mem_principalSeries3 hf] at hF
  have hTH : IsLocallyConstant fun a : Fin 3 → (v.adicCompletion ℚ)ˣ =>
      torusChar3 v χ a * halfModulus3 v a := by
    have h := hF.mul (IsLocallyConstant.const (f g)⁻¹)
    convert h using 1
    funext a
    simp only [Pi.mul_apply, Function.const_apply]
    field_simp
  have hT : IsLocallyConstant fun a : Fin 3 → (v.adicCompletion ℚ)ˣ => torusChar3 v χ a := by
    have h := hTH.mul ((isLocallyConstant_halfModulus3 v).comp fun z : ℂ => z⁻¹)
    convert h using 1
    funext a
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [mul_assoc, mul_inv_cancel₀ (halfModulus3_ne_zero v a), mul_one]
  have hc : IsLocallyConstant fun u : (v.adicCompletion ℚ)ˣ => ((χ i u : ℂˣ) : ℂ) := by
    have h := hT.comp_continuous
      (continuous_const.update i continuous_id :
        Continuous fun u : (v.adicCompletion ℚ)ˣ => Function.update (1 : Fin 3 → (v.adicCompletion ℚ)ˣ) i u)
    convert h using 1
    funext u
    exact (torusChar3_update_one v χ i u).symm
  rw [IsLocallyConstant.iff_eventually_eq] at hc ⊢
  intro u₀
  filter_upwards [hc u₀] with u hu
  exact Units.ext hu

end LanglandsTunnell.CubicInduction

end

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.charExt TateLocal.charExt_coe_units"
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "diagonal3 halfModulus3 torusChar3 principalSeries3 mem_principalSeries3_iff isLocallyConstant_of_mem_principalSeries3 apply_diagonal3_mul_of_mem_principalSeries3 rightTranslate_mem_principalSeries3 gl3Det gl3Det_ne_zero gl3Det_upperUnipotent3_mul gl3Det_diagonal3_mul cellSection charExt_units_mul cellSection_ne_zero eventually_norm_eq eventually_charExt_eq continuous_gl3Det cellSection_mem_principalSeries3 gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 LocalGL3 card_le_one_of_linearIndependent_of_upperUnipotent3_of_diagonal3_one"
namespace ScalarCommutant
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private noncomputable def gl3DetTwist (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
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

private noncomputable def principalSeries3TwistEquiv
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

private theorem exists_pair_finset_linearIndependent_of_not_exists_smul {M : Type*} [AddCommGroup M] [Module ℂ M]
    (a b : M) (ha : a ≠ 0) (hb : ¬ ∃ c : ℂ, b = c • a) :
    ∃ s : Finset M, s.card = 2 ∧ (∀ x ∈ s, x = a ∨ x = b) ∧ LinearIndependent ℂ (fun x : ↥s => (x : M)) := by
  classical
  have hba : b ≠ a := fun h => hb ⟨1, by rw [one_smul, h]⟩
  have hspan : b ∉ Submodule.span ℂ ({a} : Set M) := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact hb ⟨c, hc.symm⟩
  have hind : LinearIndepOn ℂ id (insert b ({a} : Set M)) :=
    (LinearIndepOn.singleton (R := ℂ) (v := id) (i := a) ha).id_insert hspan
  refine ⟨{b, a}, Finset.card_pair hba, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact Or.inr h
    · exact Or.inl (Finset.mem_singleton.mp h)
  · have h₂ : LinearIndepOn ℂ id ((({b, a} : Finset M) : Set M)) := by
      rw [Finset.coe_insert, Finset.coe_singleton]
      exact hind
    exact h₂

private noncomputable def rightTranslationRep
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    LocalGL3 v →* Module.End ℂ ↥(principalSeries3 v χ) where
  toFun g := (gl3AmbientRightTranslate (R := ℂ) g).restrict fun _ hf => rightTranslate_mem_principalSeries3 hf g
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

private theorem rightTranslationRep_apply_coe (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)) :
    ((rightTranslationRep v χ g f : ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ) =
      gl3AmbientRightTranslate (R := ℂ) g (f : LocalGL3 v → ℂ) := rfl

private theorem rightTranslationRep_mul_eq_mul_of_forall (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (T : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ))
    (hT : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
      (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (T f)) (g : LocalGL3 v) :
    rightTranslationRep v χ g * T = T * rightTranslationRep v χ g := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact (hT g f).symm

private theorem forall_of_rightTranslationRep_mul_eq_mul (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (T : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ))
    (hT : ∀ g : LocalGL3 v, rightTranslationRep v χ g * T = T * rightTranslationRep v χ g) (g : LocalGL3 v)
    (f : ↥(principalSeries3 v χ)) :
    (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
      gl3AmbientRightTranslate (R := ℂ) g (T f) :=
  (congrArg (fun u : ↥(principalSeries3 v χ) => (u : LocalGL3 v → ℂ)) (LinearMap.congr_fun (hT g) f)).symm

private theorem exists_eq_smul_id_of_linearEquiv {G : Type*} [Monoid G] {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (πV : G →* Module.End ℂ V) (πW : G →* Module.End ℂ W) (e : V ≃ₗ[ℂ] W) (c : G → ℂˣ)
    (he : ∀ (g : G) (x : V), e (πV g x) = (c g : ℂ) • πW g (e x))
    (hW : ∀ S : W →ₗ[ℂ] W, (∀ g : G, πW g * S = S * πW g) → ∃ a : ℂ, S = a • LinearMap.id)
    (T : V →ₗ[ℂ] V) (hT : ∀ g : G, πV g * T = T * πV g) : ∃ a : ℂ, T = a • LinearMap.id := by
  have hTapply : ∀ (g : G) (x : V), πV g (T x) = T (πV g x) := fun g x => LinearMap.congr_fun (hT g) x

  let S : W →ₗ[ℂ] W := (e : V →ₗ[ℂ] W) ∘ₗ T ∘ₗ (e.symm : W →ₗ[ℂ] V)
  have hSapply : ∀ x : V, S (e x) = e (T x) := by
    intro x
    simp [S]
  have hWg : ∀ (g : G) (x : V), πW g (e x) = ((c g)⁻¹ : ℂˣ) • e (πV g x) := by
    intro g x
    rw [he g x, Units.smul_def, smul_smul, Units.inv_mul, one_smul]
  have hS : ∀ g : G, πW g * S = S * πW g := by
    intro g
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    show πW g (S (e x)) = S (πW g (e x))
    rw [hSapply, hWg g x, Units.smul_def, map_smul, hSapply, ← hTapply, ← Units.smul_def]
    exact hWg g (T x)
  obtain ⟨a, ha⟩ := hW S hS
  refine ⟨a, LinearMap.ext fun x => ?_⟩
  have h₁ : S (e x) = a • e x := by rw [ha]; rfl
  rw [hSapply] at h₁
  apply e.injective
  rw [LinearMap.smul_apply, LinearMap.id_apply, map_smul, h₁]

private theorem exists_eq_smul_id_of_principalSeries3_equiv (v : HeightOneSpectrum (𝓞 ℚ))
    (χ χ' : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (e : ↥(principalSeries3 v χ') ≃ₗ[ℂ] ↥(principalSeries3 v χ)) (c : LocalGL3 v → ℂˣ)
    (he : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ')),
      ((e ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ :
          ↥(principalSeries3 v χ)) : LocalGL3 v → ℂ) =
        (c g : ℂ) • gl3AmbientRightTranslate (R := ℂ) g (e f))
    (hχ : ∀ T : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ),
      (∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
        (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
          gl3AmbientRightTranslate (R := ℂ) g (T f)) → ∃ a : ℂ, T = a • LinearMap.id)
    (T : ↥(principalSeries3 v χ') →ₗ[ℂ] ↥(principalSeries3 v χ'))
    (hT : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ')),
      (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (T f)) :
    ∃ a : ℂ, T = a • LinearMap.id :=
  exists_eq_smul_id_of_linearEquiv (rightTranslationRep v χ') (rightTranslationRep v χ) e c
    (fun g f => Subtype.ext (he g f))
    (fun S hS => hχ S (forall_of_rightTranslationRep_mul_eq_mul v χ S hS))
    T (rightTranslationRep_mul_eq_mul_of_forall v χ' T hT)

private noncomputable def evalOne (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) :
    ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ :=
  (LinearMap.proj (1 : LocalGL3 v) : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (principalSeries3 v χ).subtype

private theorem evalOne_apply (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : ↥(principalSeries3 v χ)) : evalOne v χ f = (f : LocalGL3 v → ℂ) 1 := rfl

private theorem rightTranslate_apply_one (v : HeightOneSpectrum (𝓞 ℚ)) (g : LocalGL3 v) (F : LocalGL3 v → ℂ) :
    gl3AmbientRightTranslate (R := ℂ) g F 1 = F g := by
  rw [gl3AmbientRightTranslate_apply, one_mul]

private theorem evalOne_translate (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)) :
    evalOne v χ ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ =
      (f : LocalGL3 v → ℂ) g :=
  rightTranslate_apply_one v g f

private theorem evalOne_comp_translate (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (S : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ))
    (hS : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
      (S ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (S f))
    (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)) :
    evalOne v χ (S ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩) =
      (S f : LocalGL3 v → ℂ) g := by
  rw [evalOne_apply, hS, rightTranslate_apply_one]

private theorem evalOne_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (f₀ : ↥(principalSeries3 v χ)) (hf₀ : f₀ ≠ 0) : evalOne v χ ≠ 0 := by
  have hf₀' : (f₀ : LocalGL3 v → ℂ) ≠ 0 := fun h => hf₀ (Subtype.ext h)
  obtain ⟨g, hg⟩ := Function.ne_iff.mp hf₀'
  intro h
  have h₁ := LinearMap.congr_fun h ⟨gl3AmbientRightTranslate (R := ℂ) g f₀, rightTranslate_mem_principalSeries3 f₀.2 g⟩
  rw [evalOne_translate, LinearMap.zero_apply] at h₁
  exact hg h₁

private theorem evalOne_comp_upperUnipotent3 (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (S : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ))
    (hS : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
      (S ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (S f))
    (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v χ)) :
    (evalOne v χ ∘ₗ S) ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
        rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = (evalOne v χ ∘ₗ S) f := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, evalOne_comp_translate v χ S hS, evalOne_apply]
  have h := (mem_principalSeries3_iff.mp (S f).2).2.1 x y z 1
  rw [mul_one] at h
  exact h

private theorem evalOne_comp_diagonal3 (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (S : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ))
    (hS : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
      (S ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (S f))
    (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v χ)) :
    (evalOne v χ ∘ₗ S) ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
        rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ =
      torusChar3 v χ a * halfModulus3 v a * (evalOne v χ ∘ₗ S) f := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, evalOne_comp_translate v χ S hS, evalOne_apply]
  have h := (mem_principalSeries3_iff.mp (S f).2).2.2 a 1
  rw [mul_one] at h
  exact h

private theorem id_comm (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)) :
    ((LinearMap.id : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ))
        ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
      gl3AmbientRightTranslate (R := ℂ) g ((LinearMap.id : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ)) f) :=
  rfl

private theorem eq_smul_id_of_evalOne_comp_eq (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (S : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ))
    (hS : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
      (S ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (S f))
    (c : ℂ) (h : evalOne v χ ∘ₗ S = c • evalOne v χ) : S = c • LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext g
  have h₁ := LinearMap.congr_fun h ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩
  rw [LinearMap.comp_apply, LinearMap.smul_apply, evalOne_comp_translate v χ S hS, evalOne_translate,
    smul_eq_mul] at h₁
  rw [h₁]
  rfl

private theorem exists_eq_smul_id_of_finset_le_one (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (f₀ : ↥(principalSeries3 v χ)) (hf₀ : f₀ ≠ 0)
    (hcard : ∀ (s : Finset (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ))
      (_hN : ∀ Λ ∈ s, ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v χ)),
        Λ ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
            rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ f)
      (_hT : ∀ Λ ∈ s, ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v χ)),
        Λ ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
            rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ =
          torusChar3 v χ a * halfModulus3 v a * Λ f)
      (_hind : LinearIndependent ℂ (fun Λ : ↥s => (Λ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ))), s.card ≤ 1)
    (S : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ))
    (hS : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
      (S ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (S f)) :
    ∃ c : ℂ, S = c • LinearMap.id := by
  by_cases hc : ∃ c : ℂ, evalOne v χ ∘ₗ S = c • (evalOne v χ ∘ₗ LinearMap.id)
  · obtain ⟨c, hc⟩ := hc
    rw [LinearMap.comp_id] at hc
    exact ⟨c, eq_smul_id_of_evalOne_comp_eq v χ S hS c hc⟩
  · exfalso
    have hne : evalOne v χ ∘ₗ LinearMap.id ≠ 0 := by
      rw [LinearMap.comp_id]
      exact evalOne_ne_zero v χ f₀ hf₀
    obtain ⟨s, hs, hmem, hind⟩ :=
      exists_pair_finset_linearIndependent_of_not_exists_smul (evalOne v χ ∘ₗ LinearMap.id) (evalOne v χ ∘ₗ S) hne hc
    have hle := hcard s ?_ ?_ hind
    · rw [hs] at hle
      exact absurd hle (by decide)
    · intro Λ hΛ x y z f
      rcases hmem Λ hΛ with rfl | rfl
      · exact evalOne_comp_upperUnipotent3 v χ LinearMap.id (id_comm v χ) x y z f
      · exact evalOne_comp_upperUnipotent3 v χ S hS x y z f
    · intro Λ hΛ a f
      rcases hmem Λ hΛ with rfl | rfl
      · exact evalOne_comp_diagonal3 v χ LinearMap.id (id_comm v χ) a f
      · exact evalOne_comp_diagonal3 v χ S hS a f

private theorem isLocallyConstant_one (v : HeightOneSpectrum (𝓞 ℚ)) (i : Fin 3) :
    IsLocallyConstant (((fun _ => 1 : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) i)) :=
  IsLocallyConstant.of_constant _ fun _ _ => rfl

private theorem exists_ne_zero_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ f₀ : ↥(principalSeries3 v (fun _ => 1)), f₀ ≠ 0 :=
  ⟨⟨cellSection v (fun _ => 1), cellSection_mem_principalSeries3 v (fun _ => 1) (isLocallyConstant_one v)⟩,
    fun h => cellSection_ne_zero v (fun _ => 1) (congrArg Subtype.val h)⟩

private theorem twist_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hall : χ 0 = χ 1 ∧ χ 1 = χ 2) :
    (fun i => χ i * (χ 0)⁻¹) = (fun _ => 1 : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) := by
  have h : ∀ i : Fin 3, χ i = χ 0 := by
    intro i
    match i with
    | 0 => rfl
    | 1 => exact hall.1.symm
    | 2 => exact (hall.1.trans hall.2).symm
  funext i
  rw [h i]
  ext x
  simp

private theorem twistEquiv_rightTranslate (v : HeightOneSpectrum (𝓞 ℚ)) (η : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hη : IsLocallyConstant η) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (g : LocalGL3 v)
    (f : ↥(principalSeries3 v χ)) :
    ((principalSeries3TwistEquiv v η hη χ
        ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ :
          ↥(principalSeries3 v fun i => χ i * η)) : LocalGL3 v → ℂ) =
      (((η (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) •
        gl3AmbientRightTranslate (R := ℂ) g (principalSeries3TwistEquiv v η hη χ f) := by
  rw [principalSeries3TwistEquiv_apply_coe, principalSeries3TwistEquiv_apply_coe, gl3AmbientRightTranslate_gl3DetTwist,
    smul_smul, Units.inv_mul, one_smul]

end LanglandsTunnell.CubicInduction.ScalarCommutant

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hall : χ 0 = χ 1 ∧ χ 1 = χ 2)
    (T : ↥(principalSeries3 v χ) →ₗ[ℂ] ↥(principalSeries3 v χ))
    (hT : ∀ (g : LocalGL3 v) (f : ↥(principalSeries3 v χ)),
      (T ⟨gl3AmbientRightTranslate (R := ℂ) g f, rightTranslate_mem_principalSeries3 f.2 g⟩ : LocalGL3 v → ℂ) =
        gl3AmbientRightTranslate (R := ℂ) g (T f)) :
    ∃ c : ℂ, T = c • LinearMap.id := by
  have hBTRIV := card_le_one_of_linearIndependent_of_upperUnipotent3_of_diagonal3_one v
  have hsmooth := isLocallyConstant_of_mem_principalSeries3_of_ne_zero v χ

  by_cases hex : ∃ f : ↥(principalSeries3 v χ), f ≠ 0
  · obtain ⟨f, hf⟩ := hex
    have hη : IsLocallyConstant (χ 0)⁻¹ := (hsmooth f 0 f.2 (fun h => hf (Subtype.ext h))).inv
    obtain ⟨f₁, hf₁⟩ := ScalarCommutant.exists_ne_zero_one v
    have htriv : ∀ (χ' : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)), χ' = (fun _ => 1) →
        ∀ S : ↥(principalSeries3 v χ') →ₗ[ℂ] ↥(principalSeries3 v χ'),
          (∀ (g : LocalGL3 v) (f' : ↥(principalSeries3 v χ')),
            (S ⟨gl3AmbientRightTranslate (R := ℂ) g f', rightTranslate_mem_principalSeries3 f'.2 g⟩ :
                LocalGL3 v → ℂ) =
              gl3AmbientRightTranslate (R := ℂ) g (S f')) →
          ∃ c : ℂ, S = c • LinearMap.id := by
      intro χ' hχ'
      subst hχ'
      intro S hS
      exact ScalarCommutant.exists_eq_smul_id_of_finset_le_one v _ f₁ hf₁ hBTRIV S hS
    exact ScalarCommutant.exists_eq_smul_id_of_principalSeries3_equiv v _ χ
      (ScalarCommutant.principalSeries3TwistEquiv v (χ 0)⁻¹ hη χ)
      (fun g => ((χ 0)⁻¹ (Matrix.GeneralLinearGroup.det g))⁻¹)
      (fun g f' => ScalarCommutant.twistEquiv_rightTranslate v (χ 0)⁻¹ hη χ g f')
      (htriv _ (ScalarCommutant.twist_eq_one v χ hall)) T hT
  · refine ⟨0, LinearMap.ext fun f => ?_⟩
    have hf : f = 0 := by
      by_contra h
      exact hex ⟨f, h⟩
    rw [hf, map_zero, LinearMap.smul_apply, LinearMap.id_apply, smul_zero]

end S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_apply_eq
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_eq_smul_id_of_gl3AmbientRightTranslate_comm_of_apply_eq (solution)
