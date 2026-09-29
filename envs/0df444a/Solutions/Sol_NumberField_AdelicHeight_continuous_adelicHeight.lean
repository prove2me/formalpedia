-- Prove2me | solution 1 for NumberField.AdelicHeight.continuous_adelicHeight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4ca34b30-f62a-597b-8eb8-64632ef6576a

import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WindowedSiegelTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicHeight_continuous_adelicHeight

set_option autoImplicit false

open NumberField NumberField.AdelicHeight AutomorphicForm

namespace P6B
namespace RFCSol

open NumberField.AdelicLevel IsDedekindDomain AutomorphicForm.WindowedSiegel

section Local

variable {K : Type*} [NormedField K]

theorem gl_coe_mul (γ g : GL (Fin 2) K) :
    ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl

variable [IsUltrametricDist K]

theorem rowMaxNorm_mul_le (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  have hentry : ∀ j : Fin 2,
      ‖((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 j‖
        ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    intro j
    rw [gl_coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hk 0 j)).trans (le_max_left _ _)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hk 1 j)).trans (le_max_right _ _)
  exact max_le (hentry 0) (hentry 1)

theorem rowMaxNorm_mul_integral (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  refine le_antisymm (rowMaxNorm_mul_le g k hk) ?_
  have h := rowMaxNorm_mul_le (g * k) k⁻¹ hk'
  rwa [mul_inv_cancel_right] at h

theorem norm_det_eq_one_of_integral (k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
  have hd : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one hk
  have hd' : ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one hk'
  have hprod : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖
      * ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← gl_coe_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      norm_one]
  refine le_antisymm hd ?_
  by_contra hlt
  push Not at hlt
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt hd'
  rw [hprod] at this
  exact lt_irrefl _ this

theorem finLocalHeight_mul_integral (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finLocalHeight (g * k) = finLocalHeight g := by
  unfold finLocalHeight
  rw [rowMaxNorm_mul_integral g k hk hk', gl_coe_mul, Matrix.det_mul, norm_mul,
    norm_det_eq_one_of_integral k hk hk', mul_one]

end Local

section Adelic

theorem finHeight_mul_integral {F : Type} [Field F] [NumberField F]
    (g k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    (hk : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ‖(finComponent (𝓞 F) F v k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1)
    (hk' : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ‖(finComponent (𝓞 F) F v k⁻¹ : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1) :
    finHeight F (g * k) = finHeight F g := by
  unfold finHeight
  refine finprod_congr fun v => ?_
  rw [map_mul]
  refine finLocalHeight_mul_integral _ _ (hk v) fun i j => ?_
  rw [← map_inv]
  exact hk' v i j

theorem norm_finComponent_le_one_of_mem (F : Type) [Field F] [NumberField F]
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hk : k ∈ finiteIntegralGL2 (𝓞 F) F) :
    (∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
        ‖(finComponent (𝓞 F) F v k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1) ∧
      ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
        ‖(finComponent (𝓞 F) F v k⁻¹ : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1 := by
  rw [mem_finiteIntegralGL2_iff] at hk
  refine ⟨fun v i j => ?_, fun v i j => ?_⟩
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.1 i j v)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.2 i j v)

theorem finHeight_mul_of_mem (F : Type) [Field F] [NumberField F]
    (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hk : k ∈ finiteIntegralGL2 (𝓞 F) F) :
    finHeight F (g * k) = finHeight F g :=
  finHeight_mul_integral g k (norm_finComponent_le_one_of_mem F hk).1
    (norm_finComponent_le_one_of_mem F hk).2

theorem isOpen_finiteIntegralGL2 (F : Type) [Field F] [NumberField F] :
    IsOpen (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
  isOpen_finiteLevelZero (𝓞 F) F top_ne_bot

theorem isLocallyConstant_finHeight (F : Type) [Field F] [NumberField F] :
    IsLocallyConstant (finHeight F) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g₀
  refine ⟨(fun g => g₀⁻¹ * g) ⁻¹' (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))),
    (isOpen_finiteIntegralGL2 F).preimage (continuous_const.mul continuous_id), ?_, fun g hg => ?_⟩
  · show g₀⁻¹ * g₀ ∈ finiteIntegralGL2 (𝓞 F) F
    rw [inv_mul_cancel]
    exact Subgroup.one_mem _
  · have h := finHeight_mul_of_mem F g₀ (k := g₀⁻¹ * g) hg
    rwa [mul_inv_cancel_left] at h

theorem continuous_finHeight (F : Type) [Field F] [NumberField F] : Continuous (finHeight F) :=
  (isLocallyConstant_finHeight F).continuous

theorem continuous_adelicHeight_impl (F : Type) [Field F] [NumberField F] :
    Continuous (adelicHeight F) := by
  unfold adelicHeight
  exact ((continuous_archHeight F).comp (continuous_glArch (𝓞 F) F)).mul
    ((continuous_finHeight F).comp (continuous_glFin (𝓞 F) F))

end Adelic

end P6B.RFCSol

theorem solution
    (F : Type) [Field F] [NumberField F] : Continuous (adelicHeight F) :=
  P6B.RFCSol.continuous_adelicHeight_impl F

#print axioms solution

end S_NumberField_AdelicHeight_continuous_adelicHeight
end P2MW
export P2MW.S_NumberField_AdelicHeight_continuous_adelicHeight (solution)
