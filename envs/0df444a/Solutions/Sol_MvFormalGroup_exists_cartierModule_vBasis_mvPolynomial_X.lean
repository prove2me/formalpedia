-- Prove2me | solution 1 for MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/aeab8434-deae-56ea-bf0b-00d56350439c

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Theorems.Thm_MvFormalGroup_exists_isComm_log_mvPolynomial_padic
import Theorems.Thm_MvFormalGroup_exists_map_padicInt_eq_of_log
import Theorems.Thm_MvFormalGroup_isComm_of_isComm_map_of_injective
import Theorems.Thm_MvFormalGroup_exists_cartierModule_vBasis_mvPolynomial_X_of_log
import Theorems.Thm_MvFormalGroup_CartierModule_isUnit_det_tangent_and_frobenius_expansion_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_cartierModule_vBasis_mvPolynomial_X

set_option autoImplicit false

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] (d : ℕ) :
    ∃ (Φ : MvFormalGroup d (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p))) (_ : Φ.IsComm)
      (f : Fin d → MvFormalGroup.CartierModule p Φ),
      IsUnit (Matrix.of fun i k => MvFormalGroup.CartierModule.tangent (f i) k).det ∧
      ∀ (i : Fin d) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p Φ,
        MvFormalGroup.CartierModule.frobenius (f i) =
          (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
            (∑ j : Fin d, MvFormalGroup.CartierModule.homothety
              (MvPolynomial.X ((m : ℕ), i, j) : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)) (f j))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] h := by
  obtain ⟨Φq, hΦc, a, f, h1, h2, h3, h4, h5⟩ :=
    MvFormalGroup.exists_isComm_log_mvPolynomial_padic p d
  obtain ⟨Φ₀, hmap⟩ :=
    MvFormalGroup.exists_map_padicInt_eq_of_log p d Φq a f h1 h2 h3 h4 h5
  have hι : Function.Injective
      (MvPolynomial.map (σ := ℕ × Fin d × Fin d) (PadicInt.Coe.ringHom (p := p))) :=
    MvPolynomial.map_injective _ Subtype.coe_injective
  have hcq : (MvFormalGroup.map
      (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) Φ₀).IsComm := by
    rw [hmap]; exact hΦc
  haveI hc : Φ₀.IsComm :=
    MvFormalGroup.isComm_of_isComm_map_of_injective _ hι Φ₀ hcq
  have h5' := h5
  rw [← hmap] at h5'
  obtain ⟨γ, hdet, hexp⟩ :=
    MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X_of_log p d Φ₀ a f h1 h2 h3 h4 h5'

  obtain ⟨hdet', hexp'⟩ :=
    MvFormalGroup.CartierModule.isUnit_det_tangent_and_frobenius_expansion_baseChange
      p ((MvPolynomial.rename (fun v : ℕ × Fin d × Fin d => (v.1, v.2.2, v.2.1))).toRingHom)
      Φ₀ γ hdet (fun m i j => MvPolynomial.X (m, j, i)) hexp
  have hXswap : ∀ (m : ℕ) (j i : Fin d),
      (MvPolynomial.rename (fun v : ℕ × Fin d × Fin d => (v.1, v.2.2, v.2.1))).toRingHom
        (MvPolynomial.X (m, j, i))
      = (MvPolynomial.X (m, i, j) : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)) :=
    fun m j i => MvPolynomial.rename_X _ _
  simp only [hXswap] at hexp'
  exact ⟨Φ₀.map ((MvPolynomial.rename (fun v : ℕ × Fin d × Fin d => (v.1, v.2.2, v.2.1))).toRingHom), MvFormalGroup.isComm_map Φ₀ ((MvPolynomial.rename (fun v : ℕ × Fin d × Fin d => (v.1, v.2.2, v.2.1))).toRingHom),
    fun i => MvFormalGroup.CartierModule.baseChange ((MvPolynomial.rename (fun v : ℕ × Fin d × Fin d => (v.1, v.2.2, v.2.1))).toRingHom) (γ i), hdet', hexp'⟩

end S_MvFormalGroup_exists_cartierModule_vBasis_mvPolynomial_X
end P2MW
export P2MW.S_MvFormalGroup_exists_cartierModule_vBasis_mvPolynomial_X (solution)
