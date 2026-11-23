-- Prove2me | solution 1 for GlobalTheory.HermLineZeros.exists_anisotropic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:21.51275+00:00
-- url     : https://prove2.me/submissions/c2989de2-3fb2-457a-99bb-69f072c28a1d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HermitianFormFiniteZerosOnLineCmExt
import Theorems.Thm_GlobalTheory_HermLineZeros_hform_expand
import Theorems.Thm_GlobalTheory_HermLineZeros_hform_single
import Theorems.Thm_GlobalTheory_HermLineZeros_conj_invol
import Theorems.Thm_GlobalTheory_HermLineZeros_exists_of_fixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace GlobalTheory.HermLineZeros
section Ring
variable {A : Type} [CommRing A] {M : ℕ}
end Ring
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
private theorem hE_self_conj_fixed (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) (v : Fin M → E) :
    σ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J v v) = _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J v v := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE _root_.Formalism.UG.hform
  rw [map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [AlgHom.coe_toRingHom, map_mul, _root_.GlobalTheory.HermLineZeros.conj_invol h, hJ.1]
  ring
end GlobalTheory.HermLineZeros
end

set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.HermLineZeros
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
namespace GlobalTheory.HermLineZeros
namespace _root_.GlobalTheory.HermLineZeros
theorem _root_.solution (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {M : ℕ} (hM : 1 ≤ M)
    {J : Matrix (Fin M) (Fin M) E} (hJ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) :
    ∃ (y : Fin M → E) (a : F), a ≠ 0 ∧ _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J y y = algebraMap F E a := by
  suffices hv : ∃ v, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J v v ≠ 0 by
    obtain ⟨v, hv⟩ := hv
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.HermLineZeros.exists_of_fixed h _ (hE_self_conj_fixed h hJ v)
    refine ⟨v, a, ?_, ha.symm⟩
    rintro rfl
    exact hv (by rw [← ha, map_zero])
  by_cases hd : ∃ i, J i i ≠ 0
  · obtain ⟨i, hi⟩ := hd
    exact ⟨Pi.single i 1, by rwa [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, _root_.GlobalTheory.HermLineZeros.hform_single]⟩
  push_neg at hd
  let i₀ : Fin M := ⟨0, hM⟩
  obtain ⟨j, hj⟩ : ∃ j, J i₀ j ≠ 0 := by
    by_contra! hrow
    exact hJ.2 (Matrix.det_eq_zero_of_row_eq_zero i₀ hrow)
  refine ⟨Pi.single i₀ 1 + (J i₀ j)⁻¹ • Pi.single j 1, ?_⟩
  have hji : J j i₀ = σ (J i₀ j) := (hJ.1 j i₀).symm
  rw [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, _root_.GlobalTheory.HermLineZeros.hform_expand, _root_.GlobalTheory.HermLineZeros.hform_single,
    _root_.GlobalTheory.HermLineZeros.hform_single, _root_.GlobalTheory.HermLineZeros.hform_single,
    _root_.GlobalTheory.HermLineZeros.hform_single, hd, hd, hji]
  simp only [AlgHom.coe_toRingHom, RingHom.coe_coe]
  rw [inv_mul_cancel₀ hj, ← map_mul, inv_mul_cancel₀ hj, map_one]
  norm_num
end _root_.GlobalTheory.HermLineZeros
end GlobalTheory.HermLineZeros
