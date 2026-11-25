-- Prove2me | solution 1 for GlobalTheory.LevelChars.heckeFin_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:59:43.382977+00:00
-- url     : https://prove2.me/submissions/ec74e887-522d-4955-81fa-28cb3d40a66f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FiniteChars
import Theorems.Thm_GlobalTheory_LevelChars_finite_chars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.LevelChars
namespace GlobalTheory.LevelChars
theorem _root_.solution
    (hA : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : Formalism.L2.Host.HChar L),
      (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) → ∀ a ∈ levSub L S N, ψ.1 a = 1)
    (hC : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N).FiniteIndex) :
    ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ)
    (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧ ∀ v ∈ S, χ.LevelLe v N}.Finite := by
  intro L _ _ I _ φ n S N hS
  classical
  rcases Set.eq_empty_or_nonempty {χ : Formalism.L2.Host.HChar L | χ.HasInf φ n ∧ (∀ v, v ∉ S → χ.UnrAt v) ∧
    ∀ v ∈ S, χ.LevelLe v N} with h | ⟨χ0, hχ0⟩
  · rw [h]; exact Set.finite_empty
  haveI := hC L S N hS
  refine ((finite_chars ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N)).preimage (f := fun χ : Formalism.L2.Host.HChar L => (χ * χ0⁻¹).1)
    (fun χ _ χ' _ h => mul_right_cancel (Subtype.ext h))).subset ?_
  intro χ hχ
  show _ ≤ MonoidHom.ker _
  refine sup_le ?_ fun a ha => MonoidHom.mem_ker.2 (hA L S N (χ * χ0⁻¹) (fun k => ?_) (fun v hv x hx => ?_) (fun v hv x hx hle => ?_) a ha)
  · rintro _ ⟨k, rfl⟩
    exact MonoidHom.mem_ker.2 ((χ * χ0⁻¹).2.2 k)
  · have e : χ.inf k = χ0.inf k := Units.ext ((hχ.1 k).trans (hχ0.1 k).symm)
    rw [Formalism.L2.Host.HChar.inf_mul, Formalism.L2.Host.HChar.inf_inv, e, mul_inv_cancel]
  · rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, hχ.2.1 v hv x hx, hχ0.2.1 v hv x hx, inv_one, one_mul]
  · rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, hχ.2.2 v hv x hx hle, hχ0.2.2 v hv x hx hle, inv_one,
      one_mul]
end GlobalTheory.LevelChars
