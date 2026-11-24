-- Prove2me | solution 1 for GlobalTheory.TamePairing.exists_apply_eq_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:45.797611+00:00
-- url     : https://prove2.me/submissions/57f67089-282e-48f4-bae5-c235befd93cd

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TamePairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
namespace GlobalTheory.TamePairing
open GlobalTheory.TameQuot
open NumberField IsDedekindDomain in
open scoped Pointwise in
private theorem ne_zero_of_isUnifRoot {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] {v : HeightOneSpectrum (𝓞 F)} {N : ℕ} [NeZero N] {x : Ω}
    (hx : _root_.GlobalTheory.TameQuot.IsUnifRoot v N x) : x ≠ 0 := by
  obtain ⟨ϖ, -, hϖ2, hxN⟩ := hx
  have hϖ : (ϖ : F) ≠ 0 := by
    intro h
    apply hϖ2
    have : ϖ = 0 := by exact_mod_cast h
    rw [this]
    exact Submodule.zero_mem _
  rintro rfl
  rw [zero_pow (NeZero.ne N), eq_comm] at hxN
  exact hϖ ((map_eq_zero_iff _ (algebraMap F Ω).injective).1 hxN)
end GlobalTheory.TamePairing
end

set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory GlobalTheory.TamePairing
open GlobalTheory.TameQuot
open NumberField IsDedekindDomain
open scoped Pointwise
namespace GlobalTheory.TamePairing
namespace _root_.GlobalTheory.TamePairing
theorem _root_.solution {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {v : HeightOneSpectrum (𝓞 F)} {N : ℕ} [NeZero N] {ζ x : Ω} (hζ : IsPrimitiveRoot ζ N)
    (hx : _root_.GlobalTheory.TameQuot.IsUnifRoot v N x) (g : _root_.Formalism.ConjugateSelfDual.G F Ω) : ∃ c : ZMod N, g x = ζ ^ c.val * x := by
  have hx0 := ne_zero_of_isUnifRoot hx
  obtain ⟨ϖ, -, -, hxN⟩ := hx
  have hpow : (g x / x) ^ N = 1 := by
    rw [div_pow, ← map_pow, hxN, AlgEquiv.commutes, div_self]
    rw [← hxN]
    exact pow_ne_zero _ hx0
  obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one hpow
  refine ⟨(i : ZMod N), ?_⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi, hi', div_mul_cancel₀ _ hx0]
end _root_.GlobalTheory.TamePairing
end GlobalTheory.TamePairing
