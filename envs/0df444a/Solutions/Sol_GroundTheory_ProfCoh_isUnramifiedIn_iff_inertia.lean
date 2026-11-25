-- Prove2me | solution 1 for GroundTheory.ProfCoh.isUnramifiedIn_iff_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:46:18.682684+00:00
-- url     : https://prove2.me/submissions/6c305ade-e4d1-4300-b71c-735b2ff51ec3

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
import Theorems.Thm_GroundTheory_ProfCoh_finiteDimensional_of_le
import Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedAt_under_iff_inertia


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
open scoped Pointwise
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
namespace GroundTheory.ProfCoh
theorem _root_.solution {E M : IntermediateField F Ω} (h : E ≤ M)
    [FiniteDimensional F M] [IsGalois F M] (v : HeightOneSpectrum (𝓞 F)) :
    Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal ↔
      ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q.LiesOver v.asIdeal →
        ∀ σ ∈ Q.inertia Gal(M/F), ∀ x (hx : x ∈ E), σ ⟨x, h hx⟩ = ⟨x, h hx⟩ := by
  have : FiniteDimensional F E := finiteDimensional_of_le h
  let _ : Algebra E M := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := NumberField.of_module_finite F M
  have := NumberField.of_module_finite F E
  constructor
  · intro hE Q hQ hQv σ hσ x hx
    have : (Q.under (𝓞 E)).LiesOver v.asIdeal := ⟨by rw [Ideal.under_under]; exact hQv.over⟩
    have hu := hE (Q.under (𝓞 E)) inferInstance this
    exact (isUnramifiedAt_under_iff_inertia Q).1 hu σ hσ ⟨x, hx⟩
  · intro hI P hP hPv
    obtain ⟨⟨Q, hQ, hQP⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 M)))
    have hQv : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
    have hu := (isUnramifiedAt_under_iff_inertia (F := F) (E := E) Q).2
      (fun σ hσ y => hI Q hQ hQv σ hσ y.1 y.2)
    have e : P = Q.under (𝓞 E) := Ideal.over_def Q P
    subst e
    exact hu
end GroundTheory.ProfCoh
