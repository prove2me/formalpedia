-- Prove2me | solution 1 for HeckeEis.exists_coeffH1par_int_modp_eigenclass_of_ideal_heckeAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/bc22a136-7b33-5d8f-902f-8b0dceeacf77

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_HeckeAlgebra

import Theorems.Thm_HeckeEis_finite_int_heckeAlgebra
import Theorems.Thm_HeckeEis_exists_coeffH1par_int_modp_eigenclass_of_eigenform
import Theorems.Thm_DeligneSerre_exists_eigencharacter_of_annihilator_le
import Theorems.Thm_CuspForm_finiteDimensional_cuspForm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_coeffH1par_int_modp_eigenclass_of_ideal_heckeAlgebra

set_option autoImplicit false

open scoped Manifold MatrixGroups

set_option synthInstance.maxHeartbeats 800000 in
open HeckeEis CongruenceSubgroup in
theorem solution
    (N : ℕ) [NeZero N] (n : ℕ) (S : Set ℕ) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpN : ¬ p ∣ N) (hn : n < p) (Q : ℕ → Prop) (a : ℕ → ℤ)
    (𝔪 : Ideal (CuspForm.heckeAlgebra N ((n : ℤ) + 2) S)) (h𝔪 : 𝔪.IsMaximal)
    (hp𝔪 : (p : CuspForm.heckeAlgebra N ((n : ℤ) + 2) S) ∈ 𝔪)
    (hocc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N), Q ℓ →
      CuspForm.heckeAlgebra.T hℓ hℓN hℓS - ((a ℓ : ℤ) : CuspForm.heckeAlgebra N ((n : ℤ) + 2) S) ∈ 𝔪) :
    ∃ y : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype),
      (¬ ∃ y' : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype), y = (p : ℤ) • y') ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N → Q ℓ →
        ∀ T : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype),
          (∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
            ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
              haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
              (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℤ n))
                  = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj ℤ n ℓ) z ∧
                T (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) →
          ∃ y' : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype), T y - (a ℓ : ℤ) • y = (p : ℤ) • y' := by
  classical
  haveI := h𝔪
  haveI : FiniteDimensional ℂ (CuspForm (Gamma0 N) ((n : ℤ) + 2)) := CuspForm.finiteDimensional_cuspForm N ((n : ℤ) + 2)
  letI instMod : Module ↥(CuspForm.heckeAlgebra N ((n : ℤ) + 2) S) (CuspForm (Gamma0 N) ((n : ℤ) + 2)) :=
    Module.compHom (CuspForm (Gamma0 N) ((n : ℤ) + 2))
      ((CuspForm.heckeAlgebra N ((n : ℤ) + 2) S).val.toRingHom :
        ↥(CuspForm.heckeAlgebra N ((n : ℤ) + 2) S) →+* Module.End ℂ (CuspForm (Gamma0 N) ((n : ℤ) + 2)))
  have hsmul : ∀ (t : ↥(CuspForm.heckeAlgebra N ((n : ℤ) + 2) S)) (f : CuspForm (Gamma0 N) ((n : ℤ) + 2)), t • f = t.1 f := fun _ _ => rfl
  haveI instSMC : SMulCommClass ↥(CuspForm.heckeAlgebra N ((n : ℤ) + 2) S) ℂ (CuspForm (Gamma0 N) ((n : ℤ) + 2)) :=
    ⟨fun t c f => by rw [hsmul, hsmul, map_smul]⟩
  haveI instFin : Module.Finite ℤ ↥(CuspForm.heckeAlgebra N ((n : ℤ) + 2) S) := HeckeEis.finite_int_heckeAlgebra N n S hS
  have hsupp : Module.annihilator ↥(CuspForm.heckeAlgebra N ((n : ℤ) + 2) S) (CuspForm (Gamma0 N) ((n : ℤ) + 2)) ≤ 𝔪 := by
    intro t ht
    rw [Module.mem_annihilator] at ht
    have h0 : t = 0 := Subtype.ext (LinearMap.ext fun f => ht f)
    rw [h0]
    exact 𝔪.zero_mem
  obtain ⟨χ, 𝔪', h𝔪', hcomap, f, hf, heig⟩ :=
    @DeligneSerre.exists_eigencharacter_of_annihilator_le (CuspForm (Gamma0 N) ((n : ℤ) + 2)) _ _ _
      ↥(CuspForm.heckeAlgebra N ((n : ℤ) + 2) S) _ instMod instSMC instFin 𝔪 h𝔪 hsupp
  refine HeckeEis.exists_coeffH1par_int_modp_eigenclass_of_eigenform N n S p Q a 𝔪' h𝔪'.isPrime ?_
    (fun ℓ => if h : ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ N then χ (CuspForm.heckeAlgebra.T h.1 h.2.2 h.2.1) else 0) f hf ?_ ?_
  · have h1 : ((p : ↥(CuspForm.heckeAlgebra N ((n : ℤ) + 2) S))) ∈ 𝔪'.comap χ := by rw [hcomap]; exact hp𝔪
    rwa [Ideal.mem_comap, map_natCast] at h1
  · intro ℓ hℓ hℓS hℓN hQ
    rw [dif_pos (show ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ N from ⟨hℓ, hℓS, hℓN⟩)]
    exact heig (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)
  · intro ℓ hℓ hℓS hℓN hQ
    rw [dif_pos (show ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ N from ⟨hℓ, hℓS, hℓN⟩)]
    have h1 := hocc ℓ hℓ hℓS hℓN hQ
    rw [← hcomap, Ideal.mem_comap, RingHom.map_sub, map_intCast] at h1
    exact h1

end S_HeckeEis_exists_coeffH1par_int_modp_eigenclass_of_ideal_heckeAlgebra
end P2MW
export P2MW.S_HeckeEis_exists_coeffH1par_int_modp_eigenclass_of_ideal_heckeAlgebra (solution)
