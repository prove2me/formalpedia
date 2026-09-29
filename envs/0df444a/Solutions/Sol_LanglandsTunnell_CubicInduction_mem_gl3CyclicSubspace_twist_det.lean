-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.mem_gl3CyclicSubspace_twist_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/96d4a04c-1c2f-5522-b1a1-1d72c9a98fb9

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_mem_gl3CyclicSubspace_twist_det

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_mem_gl3CyclicSubspace_twist_det.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "gl3AmbientRightTranslate gl3AmbientRightTranslate_apply gl3CyclicSubspace LocalGL3"
namespace TwistCyc
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable {v : HeightOneSpectrum (𝓞 ℚ)}

noncomputable def twistLin (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ) : (LocalGL3 v → ℂ) →ₗ[ℂ] (LocalGL3 v → ℂ) where
  toFun W := fun x => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x
  map_add' W₁ W₂ := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' c W := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[scoped simp] theorem twistLin_apply (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (W : LocalGL3 v → ℂ) (x : LocalGL3 v) :
    twistLin χv W x = ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x := rfl

theorem twistLin_eq (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (W : LocalGL3 v → ℂ) :
    twistLin χv W = fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x := rfl

theorem coe_det_mul (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (x h : LocalGL3 v) :
    ((χv (Matrix.GeneralLinearGroup.det (x * h)) : ℂˣ) : ℂ) =
      ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * ((χv (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) := by
  rw [map_mul, map_mul, Units.val_mul]

theorem translate_twistLin (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (h : LocalGL3 v) (W : LocalGL3 v → ℂ) :
    gl3AmbientRightTranslate (R := ℂ) h (twistLin χv W) =
      ((χv (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) • twistLin χv (gl3AmbientRightTranslate (R := ℂ) h W) := by
  funext x
  simp only [gl3AmbientRightTranslate_apply, twistLin_apply, Pi.smul_apply, smul_eq_mul, coe_det_mul]
  ring

theorem twistLin_translate (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (h : LocalGL3 v) (W : LocalGL3 v → ℂ) :
    twistLin χv (gl3AmbientRightTranslate (R := ℂ) h W) =
      (((χv (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) • gl3AmbientRightTranslate (R := ℂ) h (twistLin χv W) := by
  rw [translate_twistLin, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

theorem twistLin_inv_twistLin (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (W : LocalGL3 v → ℂ) :
    twistLin χv⁻¹ (twistLin χv W) = W := by
  funext x
  simp only [twistLin_apply, MonoidHom.inv_apply, Units.inv_mul_cancel_left]

theorem twistLin_twistLin_inv (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (W : LocalGL3 v → ℂ) :
    twistLin χv (twistLin χv⁻¹ W) = W := by
  funext x
  simp only [twistLin_apply, MonoidHom.inv_apply, Units.mul_inv_cancel_left]

theorem twistLin_mem_of_mem (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (W : LocalGL3 v → ℂ) :
    ∀ W' ∈ gl3CyclicSubspace W, twistLin χv W' ∈ gl3CyclicSubspace (twistLin χv W) := by
  intro W' hW'
  refine Submodule.span_induction (p := fun f _ => twistLin χv f ∈ gl3CyclicSubspace (twistLin χv W))
    ?_ ?_ ?_ ?_ hW'
  · rintro _ ⟨h, rfl⟩
    rw [twistLin_translate]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)
  · simp only [map_zero, Submodule.zero_mem]
  · intro f₁ f₂ _ _ h₁ h₂
    simpa only [map_add] using Submodule.add_mem _ h₁ h₂
  · intro c f _ h
    simpa only [map_smul] using Submodule.smul_mem _ c h

end LanglandsTunnell.CubicInduction.TwistCyc
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mem_gl3CyclicSubspace_twist_det.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mem_gl3CyclicSubspace_twist_det.LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_mem_gl3CyclicSubspace_twist_det.LanglandsTunnell.CubicInduction.TwistCyc"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mem_gl3CyclicSubspace_twist_det.LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_mem_gl3CyclicSubspace_twist_det.LanglandsTunnell.CubicInduction"
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_mem_gl3CyclicSubspace_twist_det.LanglandsTunnell"

open LanglandsTunnell.CubicInduction.TwistCyc in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χv : (v.adicCompletion ℚ)ˣ →* ℂˣ) (W : LocalGL3 v → ℂ) :
    (∀ W' ∈ gl3CyclicSubspace W,
        (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W' x) ∈ gl3CyclicSubspace (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x)) ∧
    (∀ W'' ∈ gl3CyclicSubspace (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x),
        ∃ W' ∈ gl3CyclicSubspace W, W'' = (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W' x)) ∧
    ((fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) = 0 ↔ W = 0) ∧
    (∀ U : Subgroup (LocalGL3 v), (∀ k ∈ U, χv (Matrix.GeneralLinearGroup.det k) = 1) →
      ∀ W' : LocalGL3 v → ℂ, (∀ k ∈ U, ∀ g : LocalGL3 v, W' (g * k) = W' g) →
        ∀ k ∈ U, ∀ g : LocalGL3 v, (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W' x) (g * k) = (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W' x) g) := by
  rw [← twistLin_eq χv W]
  refine ⟨fun W' hW' => ?_, fun W'' hW'' => ?_, ?_, ?_⟩
  · rw [← twistLin_eq χv W']
    exact twistLin_mem_of_mem χv W W' hW'
  · refine ⟨twistLin χv⁻¹ W'', ?_, ?_⟩
    · have h := twistLin_mem_of_mem χv⁻¹ (twistLin χv W) W'' hW''
      rwa [twistLin_inv_twistLin] at h
    · rw [← twistLin_eq χv (twistLin χv⁻¹ W''), twistLin_twistLin_inv]
  · constructor
    · intro h
      calc W = twistLin χv⁻¹ (twistLin χv W) := (twistLin_inv_twistLin χv W).symm
        _ = twistLin χv⁻¹ 0 := by rw [h]
        _ = 0 := map_zero _
    · rintro rfl
      exact map_zero _
  · intro U hU W' hW' k hk g
    beta_reduce
    rw [map_mul, map_mul, hU k hk, mul_one, hW' k hk g]

#print axioms solution

end S_LanglandsTunnell_CubicInduction_mem_gl3CyclicSubspace_twist_det
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_mem_gl3CyclicSubspace_twist_det (solution)
