-- Prove2me | solution 1 for GlobalTheory.UnramConjUnit.exists_sub_conj_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:15.57326+00:00
-- url     : https://prove2.me/submissions/ed0d78ff-96ae-4551-8481-d356c089dbbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsSubConjNotMem
import Theorems.Thm_GlobalTheory_UnramConjUnit_exists_sub_conj_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal GlobalTheory.SelfDualLatticeCompare
open GlobalTheory GlobalTheory.UnramConjUnit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
namespace GlobalTheory.UnramConjUnit
namespace _root_.GlobalTheory.UnramConjUnit
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    ∀ v : HeightOneSpectrum (𝓞 F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v →
    ∃ θ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v, ∃ b ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v,
      (θ - _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ θ) * b = 1 := by
  intro F E _ _ _ _ _ σ h v hv
  obtain ⟨t, d, s, hd, hs, hsv⟩ := _root_.GlobalTheory.UnramConjUnit.exists_sub_conj_notMem h v hv
  have hu : Valued.v (algebraMap F (v.adicCompletion F) (s : F)) = 1 := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [HeightOneSpectrum.adicCompletion.valued_coe]
    exact (HeightOneSpectrum.valuation_of_algebraMap v s).trans
      ((HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v s).mpr hsv)
  set u : v.adicCompletion F := algebraMap F (v.adicCompletion F) (s : F) with hu_def
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have huinv : u⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu, inv_one]
  have hintR : ∀ y : 𝓞 E, IsIntegral (v.adicCompletionIntegers F)
      ((1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (y : E)) := by
    intro y
    exact y.isIntegral_coe.map_of_comp_eq (Int.castRingHom _)
      (Algebra.TensorProduct.includeRight (R := F) (A := _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (B := E)).toRingHom
      (RingHom.ext_int _ _)
  refine ⟨(1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (t : E), hintR t,
    (u⁻¹ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E), ?_, ?_⟩
  · have hb : (u⁻¹ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E) =
        algebraMap (v.adicCompletionIntegers F) (TensorProduct F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E) ⟨u⁻¹, huinv⟩ *
          ((1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E)) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul]
      rfl
    rw [hb]
    exact isIntegral_algebraMap.mul (hintR d)
  · have hsub : (1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (t : E) -
        _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ ((1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (t : E)) =
        (1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] (d : E) := by
      simp [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hd, TensorProduct.tmul_sub]
    rw [hsub, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hs, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
    change (u * u⁻¹) ⊗ₜ[F] (1 : E) = 1
    rw [mul_inv_cancel₀ hu0]
    rfl
end _root_.GlobalTheory.UnramConjUnit
end GlobalTheory.UnramConjUnit
