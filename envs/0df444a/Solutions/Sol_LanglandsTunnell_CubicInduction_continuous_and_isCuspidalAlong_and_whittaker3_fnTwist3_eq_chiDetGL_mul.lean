-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/7747481a-f7cb-50a0-9528-e5c1003b20f5

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_FnTwist3
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.Converse

section ContinuityBlock

open IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "whittaker3 IsCuspidalAlongP21 IsCuspidalAlongP12 AdelicGL globalPointsGL centralScalarGL IsModerateGrowth3 chiDetGL norm_chiDetGL_eq_one chiDetGL_globalPointsGL_mul chiDetGL_upperUnipotent3_mul chiDetGL_radicalP21_mul chiDetGL_radicalP12_mul fnTwist3 fnTwist3_apply twistedCentralChar3 fnTwist3_centralScalarGL_mul"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

private theorem continuous_det_adelicGL :
    Continuous (Matrix.GeneralLinearGroup.det : AdelicGL 3 (𝓞 ℚ) ℚ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩

private theorem continuous_chiDetGL (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : Continuous χ) :
    Continuous (chiDetGL 3 (𝓞 ℚ) ℚ χ) := by
  unfold chiDetGL
  exact Units.continuous_val.comp (hχ.comp continuous_det_adelicGL)

private theorem continuous_fnTwist3 (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : Continuous χ)
    (form : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hcont : Continuous form) : Continuous (fnTwist3 (𝓞 ℚ) ℚ χ form) := by
  unfold fnTwist3
  exact (continuous_chiDetGL χ hχ).mul hcont

end LanglandsTunnell.CubicInduction

end ContinuityBlock

noncomputable section

namespace SlowGrowthUnderUnimodularTwist

p2m_open "NumberField LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul.LanglandsTunnell.CubicInduction"

private theorem isSlowlyIncreasingOn_mul_of_norm_eq_one {G : Type*} {S : Set G} {H : G → ℝ}
    {u φ : G → ℂ} (hu : ∀ g, ‖u g‖ = 1) (hφ : AutomorphicForm.IsSlowlyIncreasingOn S H φ) :
    AutomorphicForm.IsSlowlyIncreasingOn S H (fun g => u g * φ g) := by
  obtain ⟨C, N, hC⟩ := hφ
  refine ⟨C, N, fun g hg => ?_⟩
  rw [norm_mul, hu g, one_mul]
  exact hC g hg

private theorem isModerateGrowth3_fnTwist3 (F : Type) [Field F] [NumberField F]
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχ : AutomorphicForm.IsUnitaryChar (𝓞 F) F χ)
    {form : AdelicGL 3 (𝓞 F) F → ℂ} (hmg : IsModerateGrowth3 F form) :
    IsModerateGrowth3 F (fnTwist3 (𝓞 F) F χ form) :=
  isSlowlyIncreasingOn_mul_of_norm_eq_one (fun g => norm_chiDetGL_eq_one 3 (𝓞 F) F hχ g) hmg

end SlowGrowthUnderUnimodularTwist

end

section TransportBlock

p2m_open "Matrix IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul.LanglandsTunnell.CubicInduction MeasureTheory"

namespace DeterminantTwistTransport

private theorem fnTwist3_globalPointsGL_mul (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ)
    (form : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), form (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = form g) :
    ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      fnTwist3 (𝓞 ℚ) ℚ χ form (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = fnTwist3 (𝓞 ℚ) ℚ χ form g := by
  intro γ g
  rw [fnTwist3_apply, fnTwist3_apply, chiDetGL_globalPointsGL_mul 3 (𝓞 ℚ) ℚ hχ.1 γ g, haut γ g]

private theorem fnTwist3_centralScalarGL_mul_of_forall (ω χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (form : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * form g) :
    ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      fnTwist3 (𝓞 ℚ) ℚ χ form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) =
        (twistedCentralChar3 (𝓞 ℚ) ℚ ω χ z : ℂ) * fnTwist3 (𝓞 ℚ) ℚ χ form g :=
  fun z g => fnTwist3_centralScalarGL_mul (𝓞 ℚ) ℚ ω χ form z g (hcen z g)

private theorem isCuspidalAlongP21_fnTwist3 (pins : CarrierPins ℚ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (form : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (h : IsCuspidalAlongP21 pins form) :
    IsCuspidalAlongP21 pins (fnTwist3 (𝓞 ℚ) ℚ χ form) := by
  letI := pins.nS
  intro g
  have hg := h g
  simp only [fnTwist3_apply, chiDetGL_radicalP21_mul, integral_const_mul, hg, mul_zero]

private theorem isCuspidalAlongP12_fnTwist3 (pins : CarrierPins ℚ) (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (form : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (h : IsCuspidalAlongP12 pins form) :
    IsCuspidalAlongP12 pins (fnTwist3 (𝓞 ℚ) ℚ χ form) := by
  letI := pins.nS
  intro g
  have hg := h g
  simp only [fnTwist3_apply, chiDetGL_radicalP12_mul, integral_const_mul, hg, mul_zero]

private theorem whittaker3_fnTwist3 (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (form : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      whittaker3 pins ψ (fnTwist3 (𝓞 ℚ) ℚ χ form) g = chiDetGL 3 (𝓞 ℚ) ℚ χ g * whittaker3 pins ψ form g := by
  letI := pins.nS
  intro g
  unfold whittaker3
  simp only [fnTwist3_apply, chiDetGL_upperUnipotent3_mul, mul_assoc, integral_const_mul]

end DeterminantTwistTransport

end TransportBlock

open Matrix IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.Converse

open _root_.LanglandsTunnell.CubicInduction _root_.P2MW.S_LanglandsTunnell_CubicInduction_continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul.LanglandsTunnell.CubicInduction in

theorem solution
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (form : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcont : Continuous form)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), form (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = form g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * form g)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) form)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) form)
    (hmg : IsModerateGrowth3 ℚ form)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ) :
    Continuous (fnTwist3 (𝓞 ℚ) ℚ χ form) ∧
    (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      fnTwist3 (𝓞 ℚ) ℚ χ form (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) =
        fnTwist3 (𝓞 ℚ) ℚ χ form g) ∧
    (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      fnTwist3 (𝓞 ℚ) ℚ χ form (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) =
        (twistedCentralChar3 (𝓞 ℚ) ℚ ω χ z : ℂ) * fnTwist3 (𝓞 ℚ) ℚ χ form g) ∧
    IsCuspidalAlongP21 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) (fnTwist3 (𝓞 ℚ) ℚ χ form) ∧
    IsCuspidalAlongP12 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) (fnTwist3 (𝓞 ℚ) ℚ χ form) ∧
    IsModerateGrowth3 ℚ (fnTwist3 (𝓞 ℚ) ℚ χ form) ∧
    ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ (fnTwist3 (𝓞 ℚ) ℚ χ form) g =
        chiDetGL 3 (𝓞 ℚ) ℚ χ g * whittaker3 (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ form g := by
  exact ⟨continuous_fnTwist3 χ hχ.2.1 form hcont,
    DeterminantTwistTransport.fnTwist3_globalPointsGL_mul χ hχ form haut,
    DeterminantTwistTransport.fnTwist3_centralScalarGL_mul_of_forall ω χ form hcen,
    DeterminantTwistTransport.isCuspidalAlongP21_fnTwist3 _ χ form hP21,
    DeterminantTwistTransport.isCuspidalAlongP12_fnTwist3 _ χ form hP12,
    SlowGrowthUnderUnimodularTwist.isModerateGrowth3_fnTwist3 ℚ hχ.2.2 hmg,
    DeterminantTwistTransport.whittaker3_fnTwist3 _ ψ χ form⟩

end S_LanglandsTunnell_CubicInduction_continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_continuous_and_isCuspidalAlong_and_whittaker3_fnTwist3_eq_chiDetGL_mul (solution)
