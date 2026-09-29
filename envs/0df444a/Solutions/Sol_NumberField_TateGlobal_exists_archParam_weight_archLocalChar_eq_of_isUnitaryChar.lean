-- Prove2me | solution 1 for NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c0532935-e510-5477-9993-4b5b1ca243cc

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Theorems.Thm_LanglandsTunnell_Converse_exists_archParams_of_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_re_eq_zero_of_isArchCompAt_of_isUnitaryChar
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace Ws31
namespace ArchParam

p2m_open "NumberField.TateGlobal LanglandsTunnell.Converse NumberField.InfinitePlace.Completion"
open scoped Classical

variable (K : Type) [Field K] [NumberField K]

theorem norm_ext (w : InfinitePlace K) (x : w.Completion) :
    ‖extensionEmbedding w x‖ = ‖x‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

theorem ideleNorm_archUnitHom (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ideleNorm K (archUnitHom w x) = ‖(x : w.Completion)‖ ^ w.mult := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K (archUnitHom w x) rfl]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ w)]
  have h1 : ∀ v ∈ (Finset.univ : Finset (InfinitePlace K)).erase w,
      ‖((archUnitHom w x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v‖ ^ v.mult = 1 := by
    intro v hv
    have hvw : v ≠ w := Finset.ne_of_mem_erase hv
    show ‖Function.update (1 : InfiniteAdeleRing K) w (x : w.Completion) v‖ ^ v.mult = 1
    rw [Function.update_of_ne hvw]
    change ‖(1 : v.Completion)‖ ^ v.mult = 1
    rw [norm_one, one_pow]
  rw [Finset.prod_eq_one h1, one_mul]
  show ‖Function.update (1 : InfiniteAdeleRing K) w (x : w.Completion) w‖ ^ w.mult = _
  rw [Function.update_self]

theorem pins_of_isArchCompAt (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K) (u : ℂ) (a : ℤ)
    (h : IsArchCompAt K χ w u a) (τ : ℝ) (hu' : u = ((τ : ℝ) : ℂ) * Complex.I) :
    (∀ x : (w.Completion)ˣ,
        0 < (extensionEmbedding w (x : w.Completion)).re →
        (extensionEmbedding w (x : w.Completion)).im = 0 →
        ((archLocalChar χ w x : ℂˣ) : ℂ) =
          (((ideleNorm K (archUnitHom w x)) : ℝ) : ℂ) ^ (((τ : ℝ) : ℂ) * Complex.I)) ∧
    (∀ x : (w.Completion)ˣ,
        ‖extensionEmbedding w (x : w.Completion)‖ = 1 →
        ((archLocalChar χ w x : ℂˣ) : ℂ) = (extensionEmbedding w (x : w.Completion)) ^ a) := by
  subst hu'
  constructor
  · intro x hre him
    have hn : ‖(x : w.Completion)‖ ≠ 0 := norm_ne_zero_iff.mpr x.ne_zero
    have hnpos : 0 < ‖(x : w.Completion)‖ := norm_pos_iff.mpr x.ne_zero

    have hex : extensionEmbedding w (x : w.Completion) = ((‖(x : w.Completion)‖ : ℝ) : ℂ) := by
      have hz : extensionEmbedding w (x : w.Completion) = ((extensionEmbedding w (x : w.Completion)).re : ℂ) := by
        apply Complex.ext <;> simp [him]
      have hre' : (extensionEmbedding w (x : w.Completion)).re = ‖extensionEmbedding w (x : w.Completion)‖ := by
        rw [hz]; simp [abs_of_pos hre]
      rw [hz, hre', norm_ext]
    rw [h x, hex, div_self (by exact_mod_cast hn), one_zpow, mul_one, ideleNorm_archUnitHom]
    push_cast
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn),
      Complex.cpow_def_of_ne_zero (pow_ne_zero _ (by exact_mod_cast hn)),
      ← Complex.ofReal_pow, ← Complex.ofReal_log hnpos.le, ← Complex.ofReal_log (pow_nonneg hnpos.le _), Real.log_pow]
    push_cast
    ring_nf
  · intro x h1
    have hn1 : ‖(x : w.Completion)‖ = 1 := by rw [← norm_ext]; exact h1
    rw [h x, hn1]
    simp

theorem main (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχu : AutomorphicForm.IsUnitaryChar (𝓞 K) K χ)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) :
    ∃ (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ),
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar χ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τ v : ℝ) : ℂ) * Complex.I)) ∧
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar χ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v)) ∧
      (∀ v : InfinitePlace K, v.IsReal → m v = 0 ∨ m v = 1) := by

  have hχc' : Continuous χ := by
    refine Units.continuous_iff.mpr ⟨hχc, ?_⟩
    have : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((↑(χ z)⁻¹) : ℂ)) = fun z => ((χ z⁻¹ : ℂˣ) : ℂ) := by
      funext z; rw [map_inv]
    rw [this]; exact hχc.comp continuous_inv
  obtain ⟨uR, aR, uC, kC, hR, hC⟩ := LanglandsTunnell.Converse.exists_archParams_of_continuous K χ hχc'

  let u : InfinitePlace K → ℂ := fun w => if hw : w.IsReal then uR w hw else uC w (InfinitePlace.not_isReal_iff_isComplex.mp hw)
  let a : InfinitePlace K → ℤ := fun w => if hw : w.IsReal then ((aR w hw).val : ℤ) else kC w (InfinitePlace.not_isReal_iff_isComplex.mp hw)
  have hcomp : ∀ w, IsArchCompAt K χ w (u w) (a w) := by
    intro w
    by_cases hw : w.IsReal
    · simp only [u, a, dif_pos hw]; exact hR w hw
    · simp only [u, a, dif_neg hw]; exact hC w _
  have hre : ∀ w, (u w).re = 0 := fun w =>
    LanglandsTunnell.CubicInduction.re_eq_zero_of_isArchCompAt_of_isUnitaryChar K χ hχu w (u w) (a w) (hcomp w)
  have hu' : ∀ w, u w = (((u w).im : ℝ) : ℂ) * Complex.I := fun w => by
    apply Complex.ext <;> simp [hre w]
  refine ⟨fun w => (u w).im, a, fun w x h1 h2 => (pins_of_isArchCompAt K χ w (u w) (a w) (hcomp w) _ (hu' w)).1 x h1 h2,
    fun w x h => (pins_of_isArchCompAt K χ w (u w) (a w) (hcomp w) _ (hu' w)).2 x h, fun w hw => ?_⟩
  simp only [a, dif_pos hw]
  have := ZMod.val_lt (aR w hw)
  omega

end Ws31.ArchParam

theorem solution
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχu : AutomorphicForm.IsUnitaryChar (𝓞 K) K χ)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) :
    ∃ (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ),
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar χ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τ v : ℝ) : ℂ) * Complex.I)) ∧
      (∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar χ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (m v)) ∧
      (∀ v : InfinitePlace K, v.IsReal → m v = 0 ∨ m v = 1) :=
  Ws31.ArchParam.main K χ hχu hχc

end S_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar (solution)
